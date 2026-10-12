import NLAlib.Matrix.Norms.SpectralNormBounds

/-!
# Reindexing invariance of the matrix norms

Relabeling rows and columns by equivalences `m ≃ p`, `n ≃ q` (`Matrix.reindex`) preserves
`frobInner`, `frobSq`, `frobNorm` and `specNorm`; empty index types are allowed. These are the
transports used to move `Fin`-indexed results to arbitrary finite index types.

Source: Horn–Johnson §5.6. Atlas: `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- Relabeling rows and columns preserves the real Frobenius pairing. -/
theorem frobInner_reindex (A B : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    frobInner (A.reindex em en) (B.reindex em en) = frobInner A B := by
  simp only [frobInner, Matrix.reindex_apply, Matrix.submatrix_apply]
  calc
    (∑ i : p, ∑ j : q, A (em.symm i) (en.symm j) * B (em.symm i) (en.symm j)) =
        ∑ i : m, ∑ j : q, A i (en.symm j) * B i (en.symm j) :=
      em.symm.sum_comp (fun i => ∑ j : q, A i (en.symm j) * B i (en.symm j))
    _ = ∑ i : m, ∑ j : n, A i j * B i j :=
      Finset.sum_congr rfl (fun i _ => en.symm.sum_comp (fun j => A i j * B i j))

/-- Relabeling rows and columns preserves the squared Frobenius norm.
Horn–Johnson §5.6; atlas `norms-frob-spec`. Empty indices are allowed. -/
theorem frobSq_reindex (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    frobSq (A.reindex em en) = frobSq A :=
  frobInner_reindex A A em en

/-- Relabeling rows and columns preserves the Frobenius norm.
Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem frobNorm_reindex (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    frobNorm (A.reindex em en) = frobNorm A := by
  rw [frobNorm, frobNorm, frobSq_reindex]

private theorem reindex_frame_orth [DecidableEq m] (em : m ≃ p) :
    ((1 : Matrix m m ℝ).submatrix em.symm id)ᵀ *
      (1 : Matrix m m ℝ).submatrix em.symm id = 1 := by
  rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  simpa only [Matrix.submatrix_id_id, Matrix.mul_one] using
    Matrix.submatrix_mul_equiv (1 : Matrix m m ℝ) (1 : Matrix m m ℝ)
      id em.symm id

/-- Equivalent row and column labels preserve the spectral norm, by
orthogonal permutation frames. Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem specNorm_reindex [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    specNorm (A.reindex em en) = specNorm A := by
  let P : Matrix p m ℝ := (1 : Matrix m m ℝ).submatrix em.symm id
  let Q : Matrix q n ℝ := (1 : Matrix n n ℝ).submatrix en.symm id
  have hP : Pᵀ * P = 1 := reindex_frame_orth em
  have hQ : Qᵀ * Q = 1 := reindex_frame_orth en
  have hleft : P * A = A.submatrix em.symm id := by
    simpa only [P, Equiv.refl_symm, Equiv.coe_refl, Function.id_comp, Function.comp_id] using
      Matrix.one_submatrix_mul em.symm (Equiv.refl m) A
  have hright : (A.submatrix em.symm id) * Qᵀ = A.reindex em en := by
    rw [show Qᵀ = (1 : Matrix n n ℝ).submatrix id en.symm by
      simp only [Q, Matrix.transpose_submatrix, Matrix.transpose_one]]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.refl_symm, Equiv.coe_refl,
      Function.id_comp, Function.comp_id] using
      Matrix.mul_submatrix_one (Equiv.refl n) en.symm (A.submatrix em.symm id)
  rw [← hright, ← hleft,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hQ,
    specNorm_mul_left_of_hasOrthonormalCols hP]

end NLAlib
