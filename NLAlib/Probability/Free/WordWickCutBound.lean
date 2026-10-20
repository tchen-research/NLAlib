import NLAlib.Probability.Free.WordCreationPartialRows

/-!
# Dimension-free coefficient bound for a single Wick cut

The actual cut operator factors through the canonical scalar matrix
amplification and two contractive orthogonal creation rows. Padding on the
disjoint union of row and column indices allows rectangular cut matrices
without introducing a norm on operator-valued raw matrices.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical InnerProduct

namespace NLAlib

variable {ι : Type*} [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W

/-- The genuine operator associated with one creation/annihilation cut. -/
def wordWickCutOperator (j k : ℕ)
    (a : List.Vector ι j → List.Vector ι k → ℂ) : B :=
  ∑ u, ∑ v, a u v •
    (wordCreationProduct u.toList * star (wordCreationProduct v.toList))

private def wordWickCutMatrix (j k : ℕ)
    (a : List.Vector ι j → List.Vector ι k → ℂ) :
    Matrix (List.Vector ι j ⊕ List.Vector ι k) (List.Vector ι j ⊕ List.Vector ι k) ℂ :=
  Matrix.fromBlocks 0 a 0 0

private theorem wordWickCutOperator_eq_row_matrix_row_adjoint (j k : ℕ)
    (a : List.Vector ι j → List.Vector ι k → ℂ) :
    wordWickCutOperator j k a =
      (wordCreationRowAlong j ⟨Sum.inl, Sum.inl_injective⟩).comp
        ((wordMatrixCoefficientHom (ι := ι) (wordWickCutMatrix j k a)).comp
          (wordCreationRowAlong k ⟨Sum.inr, Sum.inr_injective⟩).adjoint) := by
  apply ContinuousLinearMap.ext
  intro x
  have hR (v : List.Vector ι k) :
      (wordCreationRowAlong k
        (⟨Sum.inr, Sum.inr_injective⟩ : List.Vector ι k ↪
          List.Vector ι j ⊕ List.Vector ι k)).adjoint x (Sum.inr v) =
        star (wordCreationProduct v.toList) x :=
    wordCreationRowAlong_adjoint_apply k _ x v
  simp [ContinuousLinearMap.comp_apply, wordCreationRowAlong_apply,
    wordMatrixCoefficientHom_apply, Fintype.sum_sum_type, wordWickCutMatrix,
    Matrix.fromBlocks, hR,
    wordWickCutOperator, ContinuousLinearMap.mul_def]

/-- Every actual Wick cut has norm at most the Euclidean norm of its
coefficient array. The bound has no dimension factor and includes zero
coefficients and empty row or column types. -/
theorem norm_wordWickCutOperator_le (j k : ℕ)
    (a : List.Vector ι j → List.Vector ι k → ℂ) :
    ‖wordWickCutOperator j k a‖ ≤ Real.sqrt (∑ u, ∑ v, ‖a u v‖ ^ 2) := by
  rw [wordWickCutOperator_eq_row_matrix_row_adjoint]
  let L := wordCreationRowAlong (ι := ι) j
    (⟨Sum.inl, Sum.inl_injective⟩ : List.Vector ι j ↪
      List.Vector ι j ⊕ List.Vector ι k)
  let R := wordCreationRowAlong (ι := ι) k
    (⟨Sum.inr, Sum.inr_injective⟩ : List.Vector ι k ↪
      List.Vector ι j ⊕ List.Vector ι k)
  let T := wordMatrixCoefficientHom (ι := ι) (wordWickCutMatrix j k a)
  change ‖L.comp (T.comp R.adjoint)‖ ≤ _
  have hL := norm_wordCreationRowAlong_le_one (ι := ι) j
    (⟨Sum.inl, Sum.inl_injective⟩ : List.Vector ι j ↪
      List.Vector ι j ⊕ List.Vector ι k)
  have hR := norm_wordCreationRowAlong_le_one (ι := ι) k
    (⟨Sum.inr, Sum.inr_injective⟩ : List.Vector ι k ↪
      List.Vector ι j ⊕ List.Vector ι k)
  have hR' : ‖R.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hR
  calc
    _ ≤ ‖L‖ * (‖T‖ * ‖R.adjoint‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) :=
      mul_le_mul hL (mul_le_mul_of_nonneg_left hR' (norm_nonneg T))
        (mul_nonneg (norm_nonneg T) (norm_nonneg R.adjoint)) zero_le_one
    _ = specNorm (wordWickCutMatrix j k a) := by
      dsimp only [T]
      rw [norm_wordMatrixCoefficientHom]
      ring
    _ ≤ frobNorm (wordWickCutMatrix j k a) := specNorm_le_frobNorm _
    _ = _ := by
      simp [frobNorm, frobSq_eq_sum_norm_sq, wordWickCutMatrix,
        Fintype.sum_sum_type, Matrix.fromBlocks]

end NLAlib
