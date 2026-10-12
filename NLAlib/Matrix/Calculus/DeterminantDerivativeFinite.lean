import NLAlib.Matrix.Calculus.DeterminantDerivative
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Principal-minor determinant derivatives on arbitrary finite labels

The adjugate diagonal is the determinant obtained by deleting the corresponding
row and column. This removes a `Fin` restriction from the characteristic
determinant derivative. Horn–Johnson §0.8.10; atlas `determinant-derivative`.
-/

noncomputable section
open scoped Matrix BigOperators Matrix.Norms.Elementwise
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An adjugate diagonal entry is the principal minor deleting that label,
over arbitrary finite indices. Empty minors have determinant one.
Horn–Johnson 2013, §0.8.10; determinant-derivative finite-index bridge. -/
theorem adjugate_apply_self_eq_det_complement (A : Matrix n n ℝ) (i : n) :
    A.adjugate i i = (A.submatrix
      (Subtype.val : {j : n // j ≠ i} → n) (Subtype.val : {j : n // j ≠ i} → n)).det := by
  classical
  let I := {j : n // j ≠ i}
  let e : I ⊕ Unit ≃ n :=
    { toFun := Sum.elim Subtype.val (fun _ => i)
      invFun := fun j => if h : j = i then Sum.inr () else Sum.inl ⟨j, h⟩
      left_inv := by
        intro j
        cases j with
        | inl j => simp [j.property]
        | inr j => cases j; simp
      right_inv := by intro j; dsimp; split_ifs with h <;> simp_all }
  let B := A.updateRow i (Pi.single i 1)
  have hBlock : B.reindex e.symm e.symm = Matrix.fromBlocks
      (A.submatrix (Subtype.val : I → n) (Subtype.val : I → n))
      (fun j (_ : Unit) => A j.val i)
      (0 : Matrix Unit I ℝ) (1 : Matrix Unit Unit ℝ) := by
    ext j k
    cases j with
    | inl j =>
      cases k with
      | inl k => simp [Matrix.reindex_apply, e, B, Matrix.fromBlocks, Matrix.updateRow_apply,
          j.property]
      | inr k => simp [Matrix.reindex_apply, e, B, Matrix.fromBlocks, Matrix.updateRow_apply,
          j.property]
    | inr j =>
      cases k with
      | inl k => simp [Matrix.reindex_apply, e, B, Matrix.fromBlocks, Matrix.updateRow_apply,
          k.property]
      | inr k => simp [Matrix.reindex_apply, e, B, Matrix.fromBlocks, Matrix.updateRow_apply,
          ]
  rw [Matrix.adjugate_apply]
  change B.det = _
  rw [← Matrix.det_reindex_self e.symm B, hBlock,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- The characteristic determinant derivative is the sum of all principal
codimension-one minors, for arbitrary finite labels and every dimension.
At dimension zero the sum is empty and the derivative is zero.
Horn–Johnson 2013, §0.8.10.
atlas: determinant-derivative -/
theorem hasDerivAt_det_smul_one_sub_sum_complement_minors (A : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (fun s => (s • (1 : Matrix n n ℝ) - A).det)
      (∑ i : n, ((t • (1 : Matrix n n ℝ) - A).submatrix
        (Subtype.val : {j : n // j ≠ i} → n)
        (Subtype.val : {j : n // j ≠ i} → n)).det) t := by
  have h := hasDerivAt_det_smul_one_sub A t
  simp only [Matrix.trace, Matrix.diag, adjugate_apply_self_eq_det_complement] at h
  exact h

end NLAlib
