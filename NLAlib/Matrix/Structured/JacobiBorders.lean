import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! # Scalar Schur-complement borders

Appending one scalar corner to a symmetric matrix has a scalar Schur complement.
The zero Schur-complement construction produces a positive semidefinite singular
border. Radau and Lobatto use this construction at the interval endpoints.
-/

noncomputable section
open Matrix Finset
open scoped Matrix MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual symmetric scalar border `[J v;vᵀ d]`, with the scalar index last. -/
def symmetricBorder (J : Matrix n n ℝ) (v : n → ℝ) (d : ℝ) :
    Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℝ :=
  fromBlocks J (of fun i _ => v i) (of fun _ j => v j) (of fun _ _ => d)

/-- The scalar Schur complement of an actual symmetric border. -/
theorem schur_symmetricBorder (J : Matrix n n ℝ) (v : n → ℝ) (d : ℝ) :
    (of (fun _ _ => d) : Matrix (Fin 1) (Fin 1) ℝ) -
      (of (fun _ j => v j) : Matrix (Fin 1) n ℝ) * J⁻¹ *
        (of (fun i _ => v i) : Matrix n (Fin 1) ℝ) =
      of (fun _ _ => d - quadForm J⁻¹ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_assoc, Matrix.mul_apply, of_apply, quadForm,
    dotProduct, mulVec, Pi.star_apply, star_trivial]

omit [Fintype n] [DecidableEq n] in
/-- The actual scalar border is Hermitian when its leading block is Hermitian. -/
theorem isHermitian_symmetricBorder {J : Matrix n n ℝ} (hJ : J.IsHermitian)
    (v : n → ℝ) (d : ℝ) : (symmetricBorder J v d).IsHermitian := by
  apply hJ.fromBlocks
  · ext i j
    simp only [conjTranspose_apply, of_apply, star_trivial]
  · ext i j
    simp only [conjTranspose_apply, of_apply, star_trivial]

omit [Fintype n] in
/-- Scalar identity shifts of the actual border keep the cross-block vector fixed. -/
theorem symmetricBorder_sub_smul_one (J : Matrix n n ℝ) (v : n → ℝ) (d z : ℝ) :
    symmetricBorder J v d - z • 1 = symmetricBorder (J - z • 1) v (d - z) := by
  ext (i | i) (j | j)
  · simp [symmetricBorder, Matrix.one_apply]
  · simp [symmetricBorder]
  · simp [symmetricBorder]
  · simp [symmetricBorder, Subsingleton.elim i j]

omit [Fintype n] in
/-- Negating a shifted border changes the cross vector sign. -/
theorem smul_one_sub_symmetricBorder (J : Matrix n n ℝ) (v : n → ℝ) (d z : ℝ) :
    z • 1 - symmetricBorder J v d = symmetricBorder (z • 1 - J) (-v) (z - d) := by
  ext (i | i) (j | j)
  · simp [symmetricBorder, Matrix.one_apply]
  · simp [symmetricBorder]
  · simp [symmetricBorder]
  · simp [symmetricBorder, Subsingleton.elim i j]

/-- For a positive definite leading block, actual border positivity is exactly
the scalar Schur-complement inequality. Source: focused reroutes, Section 3 (BL4), (BL9).
atlas: gauss-radau-lobatto (partial) -/
theorem posSemidef_symmetricBorder_iff {J : Matrix n n ℝ} (hJ : J.PosDef)
    (v : n → ℝ) (d : ℝ) :
    (symmetricBorder J v d).PosSemidef ↔ quadForm J⁻¹ v ≤ d := by
  let : Invertible J := hJ.isUnit.invertible
  have h := Matrix.PosDef.fromBlocks₁₁ (of (fun i _ => v i) : Matrix n (Fin 1) ℝ)
    (of (fun _ _ => d) : Matrix (Fin 1) (Fin 1) ℝ) hJ
  have hv : (of (fun i _ => v i) : Matrix n (Fin 1) ℝ)ᴴ = of (fun _ j => v j) := by
    ext i j
    simp
  rw [hv, schur_symmetricBorder] at h
  change (symmetricBorder J v d).PosSemidef ↔ _ at h
  rw [h]
  have heq : (of (fun _ _ => d - quadForm J⁻¹ v) : Matrix (Fin 1) (Fin 1) ℝ) =
      diagonal (fun _ => d - quadForm J⁻¹ v) := by
    ext i j
    simp [Subsingleton.elim i j]
  rw [heq, posSemidef_diagonal_iff]
  simp only [sub_nonneg]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- A zero scalar Schur complement gives an actual PSD singular border.
Source: focused mathematical reroutes, Section 3 (BL4), (BL9).
atlas: gauss-radau-lobatto (partial) -/
theorem posSemidef_and_det_eq_zero_symmetricBorder_of_schur_zero
    {J : Matrix n n ℝ} (hJ : J.PosDef) (v : n → ℝ) :
    (symmetricBorder J v (quadForm J⁻¹ v)).PosSemidef ∧
      (symmetricBorder J v (quadForm J⁻¹ v)).det = 0 := by
  refine ⟨(posSemidef_symmetricBorder_iff hJ v _).mpr le_rfl, ?_⟩
  let : Invertible J := hJ.isUnit.invertible
  rw [symmetricBorder, Matrix.det_fromBlocks₁₁, invOf_eq_nonsing_inv, schur_symmetricBorder]
  simp

end NLAlib
