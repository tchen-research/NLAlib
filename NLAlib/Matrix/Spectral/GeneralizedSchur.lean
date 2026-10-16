import NLAlib.Matrix.Spectral.ComplexQZ
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!+# Generalized Schur determinant and projective eigenvalues

The full complex QZ existence theorem includes every singular pencil.
Its triangular diagonals factor the homogeneous determinant. Regularity
is exactly exclusion of zero diagonal pairs; zero second coordinates
therefore encode the eigenvalue at infinity without dividing by them.

Source: Horn–Johnson (2013), §2.6; matrix-toolkit re-derivation §38.
Atlas: `generalized-schur-qz`.
-/
noncomputable section
open Matrix Polynomial
open scoped Matrix
namespace NLAlib
variable {n : ℕ} {A B S T : Matrix (Fin n) (Fin n) ℂ}
  {Q Z : Matrix.unitaryGroup (Fin n) ℂ}

/-- The determinant polynomial of the square pencil `A - λB`. -/
def pencilPolynomial (A B : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  (A.map (Polynomial.C : ℂ →+* Polynomial ℂ) - (Polynomial.X : Polynomial ℂ) • B.map (Polynomial.C : ℂ →+* Polynomial ℂ)).det

/-- The homogeneous determinant factors through the two QZ diagonals.
The product includes multiplicities and is `1` in dimension zero.
atlas: generalized-schur-qz (partial) -/
theorem det_smul_sub_smul_of_unitary_qz
    (hA : A = (Q : Matrix (Fin n) (Fin n) ℂ) * S * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hB : B = (Q : Matrix (Fin n) (Fin n) ℂ) * T * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (α β : ℂ) :
    (β • A - α • B).det = (Q : Matrix (Fin n) (Fin n) ℂ).det *
      (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ.det * ∏ i, (β * S i i - α * T i i) := by
  have hf : β • A - α • B = (Q : Matrix (Fin n) (Fin n) ℂ) *
      (β • S - α • T) * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_mul, ← hA, ← hB]
  have hu : (β • S - α • T).IsUpperTriangular := by
    intro i j hij
    simp [Matrix.sub_apply, Matrix.smul_apply, hS hij, hT hij]
  rw [hf, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_isUpperTriangular hu]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The affine determinant polynomial has the complete factor list given
by the QZ diagonal pairs, with characteristic multiplicities.
atlas: generalized-schur-qz (partial) -/
theorem pencilPolynomial_eq_prod_of_unitary_qz
    (hA : A = (Q : Matrix (Fin n) (Fin n) ℂ) * S * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hB : B = (Q : Matrix (Fin n) (Fin n) ℂ) * T * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) :
    pencilPolynomial A B = Polynomial.C ((Q : Matrix (Fin n) (Fin n) ℂ).det *
      (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ.det) *
      ∏ i, (Polynomial.C (S i i) - Polynomial.X * Polynomial.C (T i i)) := by
  have hf : A.map (Polynomial.C : ℂ →+* Polynomial ℂ) - (Polynomial.X : Polynomial ℂ) • B.map (Polynomial.C : ℂ →+* Polynomial ℂ) =
      (Q : Matrix (Fin n) (Fin n) ℂ).map (Polynomial.C : ℂ →+* Polynomial ℂ) *
        (S.map (Polynomial.C : ℂ →+* Polynomial ℂ) - (Polynomial.X : Polynomial ℂ) • T.map (Polynomial.C : ℂ →+* Polynomial ℂ)) *
        ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ).map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [hA, hB, Matrix.map_mul]
  have hu : (S.map (Polynomial.C : ℂ →+* Polynomial ℂ) - (Polynomial.X : Polynomial ℂ) • T.map (Polynomial.C : ℂ →+* Polynomial ℂ)).IsUpperTriangular := by
    intro i j hij
    simp [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, hS hij, hT hij]
  unfold pencilPolynomial
  rw [hf, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_isUpperTriangular hu]
  have hmap (M : Matrix (Fin n) (Fin n) ℂ) :
      (M.map (Polynomial.C : ℂ →+* Polynomial ℂ)).det = Polynomial.C M.det := ((Polynomial.C : ℂ →+* Polynomial ℂ).map_det M).symm
  rw [hmap, hmap, map_mul]
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A pencil is regular exactly when none of its QZ diagonal pairs is
simultaneously zero. Singular and empty pencils are covered by the equivalence.
atlas: generalized-schur-qz (partial) -/
theorem pencilPolynomial_ne_zero_iff_of_unitary_qz
    (hA : A = (Q : Matrix (Fin n) (Fin n) ℂ) * S * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hB : B = (Q : Matrix (Fin n) (Fin n) ℂ) * T * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) :
    pencilPolynomial A B ≠ 0 ↔ ∀ i, S i i ≠ 0 ∨ T i i ≠ 0 := by
  have hc : Polynomial.C ((Q : Matrix (Fin n) (Fin n) ℂ).det *
      (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ.det) ≠ 0 := by
    apply Polynomial.C_ne_zero.mpr
    apply mul_ne_zero
    · exact (Matrix.isUnit_det_of_right_inverse (Unitary.coe_mul_star_self Q)).ne_zero
    · exact (Matrix.isUnit_det_of_right_inverse (Unitary.coe_star_mul_self Z)).ne_zero
  rw [pencilPolynomial_eq_prod_of_unitary_qz hA hB hS hT, mul_ne_zero_iff,
    and_iff_right hc, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_const]
  apply forall_congr'
  intro i
  have hz : Polynomial.C (S i i) - Polynomial.X * Polynomial.C (T i i) = 0 ↔
      S i i = 0 ∧ T i i = 0 := by
    constructor
    · intro he
      have h0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) he
      have h1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) he
      simpa using And.intro h0 h1
    · rintro ⟨hs, ht⟩
      simp [hs, ht]
  simpa only [not_and_or] using (not_congr hz)

/-- The homogeneous roots are precisely the QZ diagonal pairs. Under
regularity these pairs define the complete projective eigenvalue list,
including infinity (`β = 0`), without any division by a diagonal entry.
atlas: generalized-schur-qz (partial) -/
theorem det_smul_sub_smul_eq_zero_iff_of_unitary_qz
    (hA : A = (Q : Matrix (Fin n) (Fin n) ℂ) * S * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hB : B = (Q : Matrix (Fin n) (Fin n) ℂ) * T * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (α β : ℂ) :
    (β • A - α • B).det = 0 ↔ ∃ i, β * S i i = α * T i i := by
  have hQ : (Q : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (Unitary.coe_mul_star_self Q)).ne_zero
  have hZ : (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ.det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (Unitary.coe_star_mul_self Z)).ne_zero
  rw [det_smul_sub_smul_of_unitary_qz hA hB hS hT, mul_eq_zero,
    or_iff_right (mul_ne_zero hQ hZ), Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, sub_eq_zero]

end NLAlib


