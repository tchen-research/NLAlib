import NLAlib.Matrix.OrderedSchur
import NLAlib.Matrix.SchurFrobenius
import NLAlib.Matrix.SchurDensity
import NLAlib.Matrix.SmallTriangularSimilarity
import NLAlib.Matrix.RealSpectrumSchur
import NLAlib.Matrix.RealSchurSimilarity
import NLAlib.Matrix.ComplexQZ
import NLAlib.Matrix.RealQZ

/-!
# The Schur and generalized Schur toolkit

Prescribed complex order, the corrected real form and real-spectrum case,
the exact Frobenius identity, density of distinct spectra, almost diagonal
similarity, and both complex and real QZ for arbitrary square pencils.
Source: Horn–Johnson (2013), §§2.3, 2.4 and 2.6.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.Frobenius

namespace NLAlib

/-- The complete Schur toolkit, including the corrected real two-dimensional
blocks with equal diagonals and negative off-diagonal product, arbitrary
prescribed complex root order, real triangularization for real complex
spectrum, the Frobenius identity and equality criterion, real and complex
distinct-spectrum density, small-entry similarities and both QZ forms.
Source: Horn–Johnson (2013), Theorems 2.3.1, 2.3.4, 2.4.7.1–2.4.7.2 and
2.6.1–2.6.2. Empty shapes and singular pencils are included.
atlas: schur-triangularization -/
theorem schur_triangularization_properties
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (Ar Br : Matrix n n ℝ) (e : Fin (Fintype.card n) ≃ n) :
    (∀ d : n → ℂ, A.charpoly = ∏ i, (X - C (d i)) →
      ∃ (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ),
        A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ ∧
        (∀ i j, e.symm j < e.symm i → T i j = 0) ∧ ∀ i, T i i = d i) ∧
    (∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ Ar = Q * T * Qᵀ ∧
      IsRealSchurForm (T.submatrix e e)) ∧
    ((∀ μ ∈ spectrum ℂ (Ar.map Complex.ofReal), μ.im = 0) →
      ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ Ar = Q * T * Qᵀ ∧
        (∀ i j, e.symm j < e.symm i → T i j = 0) ∧
        Ar.charpoly = ∏ i, (X - C (T i i))) ∧
    (∀ (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ),
      A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ →
      A.charpoly = ∏ i, (X - C (T i i)) →
      ‖A‖ ^ 2 = (∑ i, ‖T i i‖ ^ 2) + ‖T - Matrix.diagonal T.diag‖ ^ 2 ∧
      (∑ i, ‖T i i‖ ^ 2) ≤ ‖A‖ ^ 2 ∧
      ((∑ i, ‖T i i‖ ^ 2) = ‖A‖ ^ 2 ↔ A * Aᴴ = Aᴴ * A)) ∧
    (Dense {M : Matrix n n ℂ | ∃ d : n → ℂ, Function.Injective d ∧
      M.charpoly = ∏ i, (X - C (d i))}) ∧
    (Dense {M : Matrix n n ℝ | ∃ d : n → ℂ, Function.Injective d ∧
      (M.map Complex.ofReal).charpoly = ∏ i, (X - C (d i))}) ∧
    (∀ ε : ℝ, 0 < ε → ∃ S : Matrix n n ℂ, IsUnit S ∧
      (∀ i j, e.symm j < e.symm i → (S⁻¹ * A * S) i j = 0) ∧
      (∀ i j, e.symm i < e.symm j → ‖(S⁻¹ * A * S) i j‖ < ε)) ∧
    ((∀ μ ∈ spectrum ℂ (Ar.map Complex.ofReal), μ.im = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ S : Matrix n n ℝ, IsUnit S ∧
        (∀ i j, e.symm j < e.symm i → (S⁻¹ * Ar * S) i j = 0) ∧
        (∀ i j, e.symm i < e.symm j → ‖(S⁻¹ * Ar * S) i j‖ < ε)) ∧
    (∃ V W : Matrix.unitaryGroup n ℂ, ∃ T₁ T₂ : Matrix n n ℂ,
      A = (V : Matrix n n ℂ) * T₁ * (W : Matrix n n ℂ)ᴴ ∧
      B = (V : Matrix n n ℂ) * T₂ * (W : Matrix n n ℂ)ᴴ ∧
      (∀ i j, e.symm j < e.symm i → T₁ i j = 0) ∧
      (∀ i j, e.symm j < e.symm i → T₂ i j = 0)) ∧
    (∃ V W T₁ T₂ : Matrix n n ℝ, HasOrthonormalCols V ∧ HasOrthonormalCols W ∧
      Ar = V * T₁ * Wᵀ ∧ Br = V * T₂ * Wᵀ ∧
      IsUpperQuasiTriangular (T₁.submatrix e e) ∧
      (∀ i j, e.symm j < e.symm i → T₂ i j = 0)) := by
  refine ⟨fun d hd => exists_unitary_schur_triangularization_with_charpoly A e d hd,
    exists_orthogonal_real_schur Ar e,
    fun h => exists_orthogonal_triangularization_of_complex_spectrum_real Ar e h,
    ?_, dense_exists_injective_charpoly_factors_complex,
    dense_exists_injective_charpoly_factors_real,
    fun _ hε => exists_similarity_upper_triangular_small_entries A e hε,
    fun h _ hε => exists_real_similarity_upper_triangular_small_entries Ar e h hε,
    exists_unitary_qz_triangularization A B e,
    exists_orthogonal_qz_triangularization Ar Br e⟩
  intro U T hA hchar
  refine ⟨?_, sum_norm_sq_schur_diagonal_le_frobenius_norm_sq U T hA,
    sum_norm_sq_schur_diagonal_eq_iff_normal U T hA hchar⟩
  rw [hA, frobenius_norm_sq_unitary_similarity]
  exact frobenius_norm_sq_eq_diagonal_add_off_diagonal T

end NLAlib
