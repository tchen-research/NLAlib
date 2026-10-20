import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Algebra.Spectrum.Pi
import Mathlib.Data.Matrix.Block

/-! # Actual spectra of native C*-matrix diagonal blocks

The literal block-diagonal map is a unital injective star-algebra map.
Spectral permanence therefore identifies its real self-adjoint spectrum
with the union of the two actual block spectra, including continuous
spectra and empty finite coordinate types.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CStarMatrix
variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A]

/-- Literal native block-diagonal matrices, as a genuine unital
star-algebra embedding of the product of the two matrix algebras. -/
def blockDiagonalStarAlgHom :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₐ[ℂ]
      CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun P := ofMatrix (Matrix.fromBlocks (ofMatrix.symm P.1) 0 0 (ofMatrix.symm P.2))
  map_one' := by
    change ofMatrix (Matrix.fromBlocks 1 0 0 1) = (1 : CStarMatrix (m ⊕ n) (m ⊕ n) A)
    rw [Matrix.fromBlocks_one]
    rfl
  map_mul' P Q := by
    change Matrix.fromBlocks (ofMatrix.symm P.1 * ofMatrix.symm Q.1) 0 0
      (ofMatrix.symm P.2 * ofMatrix.symm Q.2) =
        Matrix.fromBlocks (ofMatrix.symm P.1) 0 0 (ofMatrix.symm P.2) *
          Matrix.fromBlocks (ofMatrix.symm Q.1) 0 0 (ofMatrix.symm Q.2)
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
  map_zero' := by
    ext (i | i) (j | j) <;> rfl
  map_add' P Q := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  commutes' z := by
    ext (i | i) (j | j) <;> simp [CStarMatrix.algebraMap_apply, Matrix.fromBlocks]
  map_star' P := by
    ext (i | i) (j | j) <;> simp [CStarMatrix.star_apply, Matrix.fromBlocks]

/-- The native block-diagonal product map is injective, with no nonempty
coordinate assumptions. -/
theorem blockDiagonalStarAlgHom_injective :
    Function.Injective (blockDiagonalStarAlgHom (m := m) (n := n) (A := A)) := by
  intro P Q h
  apply Prod.ext
  · apply CStarMatrix.ext
    intro i j
    exact congrArg (fun T : CStarMatrix (m ⊕ n) (m ⊕ n) A => T (.inl i) (.inl j)) h
  · apply CStarMatrix.ext
    intro i j
    exact congrArg (fun T : CStarMatrix (m ⊕ n) (m ⊕ n) A => T (.inr i) (.inr j)) h

variable [PartialOrder A] [StarOrderedRing A]

/-- The actual real spectrum of a self-adjoint native diagonal block is
the union of its actual block spectra. This applies to arbitrary C*-algebra
entries, and does not enumerate eigenvalues or assume finite spectra. -/
theorem spectrum_real_blockDiagonal (P : CStarMatrix m m A) (Q : CStarMatrix n n A)
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) :
    spectrum ℝ (blockDiagonalStarAlgHom (P, Q)) = spectrum ℝ P ∪ spectrum ℝ Q := by
  have hPQ : IsSelfAdjoint (P, Q) := by
    change (star P, star Q) = (P, Q)
    rw [hP.star_eq, hQ.star_eq]
  exact (hPQ.map_spectrum_real (blockDiagonalStarAlgHom (m := m) (n := n) (A := A))
    (blockDiagonalStarAlgHom_injective (m := m) (n := n) (A := A))).trans
    (Prod.spectrum_eq P Q)

end CStarMatrix
