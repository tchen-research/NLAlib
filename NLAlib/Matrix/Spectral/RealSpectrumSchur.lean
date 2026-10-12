import NLAlib.Matrix.Spectral.OrderedSchur
import NLAlib.Matrix.Spectral.SmallTriangularSimilarity
import NLAlib.Matrix.Subspaces.Projections
/-!
# Real triangular Schur forms from real complex spectra

If the complexification has only real spectral points, its complete complex
root list descends coefficientwise to a real characteristic factorization.
The real instance of ordered Schur then gives an orthogonal triangular form.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real matrix whose complex spectrum is real has a complete real
characteristic-root list with multiplicity. Source: Horn–Johnson (2013),
Theorem 2.3.1; repeated roots and empty shapes are allowed. -/
theorem exists_real_charpoly_factors_of_complex_spectrum_real
    (A : Matrix n n ℝ)
    (hreal : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.im = 0) :
    ∃ d : n → ℝ, A.charpoly = ∏ i, (X - C (d i)) := by
  classical
  obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization
    (A.map Complex.ofReal) (Fintype.equivFin n).symm
  let d : n → ℝ := fun i => (T i i).re
  have hval (i : n) : (d i : ℂ) = T i i := by
    have hroot : (A.map Complex.ofReal).charpoly.IsRoot (T i i) := by
      rw [hchar]
      simp only [Polynomial.IsRoot, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have him := hreal (T i i) (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot)
    apply Complex.ext
    · rfl
    · exact him.symm
  refine ⟨d, ?_⟩
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  have hmap : (A.map Complex.ofReal).charpoly = A.charpoly.map Complex.ofRealHom :=
    Matrix.charpoly_map A Complex.ofRealHom
  rw [← hmap, hchar, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Complex.ofRealHom_eq_coe, hval]

/-- A real matrix with real complex spectrum has a real orthogonal upper
triangular Schur form. Source: Horn–Johnson (2013), Theorem 2.3.1;
the diagonal factorization records every characteristic root with multiplicity.
atlas: schur-triangularization (partial) -/
theorem exists_orthogonal_triangularization_of_complex_spectrum_real
    (A : Matrix n n ℝ) (e : Fin (Fintype.card n) ≃ n)
    (hreal : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.im = 0) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      (∀ i j, e.symm j < e.symm i → T i j = 0) ∧
      A.charpoly = ∏ i, (X - C (T i i)) := by
  obtain ⟨d, hd⟩ := exists_real_charpoly_factors_of_complex_spectrum_real A hreal
  obtain ⟨U, T, hA, htri, hdiag⟩ := exists_unitary_schur_triangularization_with_charpoly A e d hd
  have hUt : (U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self U
  have hU : HasOrthonormalCols (U : Matrix n n ℝ) := by
    simpa only [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial] using hUt
  refine ⟨U, T, hU, ?_, htri, ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  · simpa only [hdiag] using hd

/-- When a real matrix has real complex spectrum, a real similarity can
make all strict upper entries smaller than any positive epsilon. Source:
Horn–Johnson (2013), §2.3; this retains the real scalar field of the similarity.
atlas: schur-triangularization (partial) -/
theorem exists_real_similarity_upper_triangular_small_entries
    (A : Matrix n n ℝ) (e : Fin (Fintype.card n) ≃ n)
    (hreal : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.im = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℝ, IsUnit S ∧
      (∀ i j, e.symm j < e.symm i → (S⁻¹ * A * S) i j = 0) ∧
      (∀ i j, e.symm i < e.symm j → ‖(S⁻¹ * A * S) i j‖ < ε) := by
  obtain ⟨Q, T, hQ, hA, htri, _⟩ := exists_orthogonal_triangularization_of_complex_spectrum_real A e hreal
  have hQu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hQ)
  have hInv : Q⁻¹ = Qᵀ := Matrix.inv_eq_left_inv hQ
  have hsim : Q⁻¹ * A * Q = T := by
    rw [hInv, hA]
    rw [Matrix.mul_assoc Q T Qᵀ, ← Matrix.mul_assoc Qᵀ Q, hQ,
      Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one]
  exact exists_similarity_small_entries_of_triangular_similarity A Q hQu e
    (fun i j hij => by rw [hsim]; exact htri i j hij) hε

end NLAlib
