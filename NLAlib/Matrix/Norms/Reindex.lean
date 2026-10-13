import NLAlib.Matrix.Norms.SpectralNormBounds

/-!
# Reindexing invariance of the matrix norms

Relabeling rows and columns by equivalences `m ≃ p`, `n ≃ q` (`Matrix.reindex`) preserves
`frobInner`, `frobSq`, `frobNorm` and `specNorm`; empty index types are allowed. These are the
transports used to move `Fin`-indexed results to arbitrary finite index types.

Source: Horn–Johnson §5.6. Atlas: `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Relabeling rows and columns preserves the Frobenius pairing, over `ℝ` or `ℂ`. -/
theorem frobInner_reindex (A B : Matrix m n 𝕜) (em : m ≃ p) (en : n ≃ q) :
    frobInner (A.reindex em en) (B.reindex em en) = frobInner A B := by
  simp only [frobInner, Matrix.reindex_apply, Matrix.submatrix_apply]
  congr 1
  calc
    (∑ i : p, ∑ j : q, star (A (em.symm i) (en.symm j)) * B (em.symm i) (en.symm j)) =
        ∑ i : m, ∑ j : q, star (A i (en.symm j)) * B i (en.symm j) :=
      em.symm.sum_comp (fun i => ∑ j : q, star (A i (en.symm j)) * B i (en.symm j))
    _ = ∑ i : m, ∑ j : n, star (A i j) * B i j :=
      Finset.sum_congr rfl (fun i _ => en.symm.sum_comp (fun j => star (A i j) * B i j))

/-- Relabeling rows and columns preserves the squared Frobenius norm, over `ℝ` or `ℂ`.
Horn–Johnson §5.6; atlas `norms-frob-spec`. Empty indices are allowed. -/
theorem frobSq_reindex (A : Matrix m n 𝕜) (em : m ≃ p) (en : n ≃ q) :
    frobSq (A.reindex em en) = frobSq A :=
  frobInner_reindex A A em en

open scoped Matrix.Norms.L2Operator in
/-- Relabeling rows and columns preserves the Frobenius norm, over `ℝ` or `ℂ`.
Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem frobNorm_reindex (A : Matrix m n 𝕜) (em : m ≃ p) (en : n ≃ q) :
    frobNorm (A.reindex em en) = frobNorm A := by
  rw [frobNorm, frobNorm, frobSq_reindex]

open scoped Matrix.Norms.L2Operator in
private theorem reindex_frame_orth [DecidableEq m] (em : m ≃ p) :
    ((1 : Matrix m m 𝕜).submatrix em.symm id)ᴴ *
      (1 : Matrix m m 𝕜).submatrix em.symm id = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  simpa only [Matrix.submatrix_id_id, Matrix.mul_one] using
    Matrix.submatrix_mul_equiv (1 : Matrix m m 𝕜) (1 : Matrix m m 𝕜)
      id em.symm id

open scoped Matrix.Norms.L2Operator in
/-- Equivalent row and column labels preserve the spectral norm, by
unitary permutation frames; over `ℝ` or `ℂ`. Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem specNorm_reindex [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n 𝕜) (em : m ≃ p) (en : n ≃ q) :
    specNorm (A.reindex em en) = specNorm A := by
  let P : Matrix p m 𝕜 := (1 : Matrix m m 𝕜).submatrix em.symm id
  let Q : Matrix q n 𝕜 := (1 : Matrix n n 𝕜).submatrix en.symm id
  have hP : Pᴴ * P = 1 := reindex_frame_orth em
  have hQ : Qᴴ * Q = 1 := reindex_frame_orth en
  have hleft : P * A = A.submatrix em.symm id := by
    simpa only [P, Equiv.refl_symm, Equiv.coe_refl, Function.id_comp, Function.comp_id] using
      Matrix.one_submatrix_mul em.symm (Equiv.refl m) A
  have hright : (A.submatrix em.symm id) * Qᴴ = A.reindex em en := by
    rw [show Qᴴ = (1 : Matrix n n 𝕜).submatrix id en.symm by
      simp only [Q, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.refl_symm, Equiv.coe_refl,
      Function.id_comp, Function.comp_id] using
      Matrix.mul_submatrix_one (Equiv.refl n) en.symm (A.submatrix em.symm id)
  rw [← hright, ← hleft,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hQ,
    specNorm_mul_left_of_hasOrthonormalCols hP]

/-- Equivalent row, middle, and column labels commute with rectangular matrix
multiplication. Mathlib's submatrix multiplication transport; supports
`wedin-sin-theta` on arbitrary finite coordinate labels. -/
theorem mul_reindex {m n p m' n' p' : Type*} [Fintype n] [Fintype n']
    (A : Matrix m n ℝ) (B : Matrix n p ℝ)
    (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p') :
    (A * B).reindex em ep = A.reindex em en * B.reindex en ep := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

end NLAlib
