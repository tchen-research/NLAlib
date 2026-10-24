import NLAlib.Matrix.Norms.NuclearPSD
import NLAlib.Matrix.Norms.SchattenFrames
import NLAlib.Matrix.Spectral.EckartYoung
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Nuclear tails and square-root Frobenius tails

The nuclear error of the chosen truncated SVD is the sum of the omitted singular values.
For a PSD matrix it is the optimal squared Frobenius error of its positive square root.
Both scalar identities hold at repeated singular values without choosing compatible SVDs.

Source: the Gram correspondence in Martinsson–Tropp 2020, §14.2. The square-root identity
follows `NLA-lib/NLAlib`, `Matrix/Functions/AbsoluteValue.lean`, commit
`6a845a2ec27f37c1a98118c107a06a13ce45273d` (Apache-2.0), using the backend's native SVD.
It supplies the remaining tail identification for atlas `nystrom-randomized`.
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The nuclear error of the chosen top-`k` singular-value truncation of a real square matrix
is its singular-value tail. The value is independent of singular-vector choices, including
ties. This is the nuclear analogue of the native Frobenius tail identity. -/
theorem nuclearNorm_sub_truncatedSVD_eq_sum (A : Matrix n n ℝ) (k : ℕ) :
    nuclearNorm (A - truncatedSVD A k) =
      ∑ i : Fin (Fintype.card n), if k ≤ (i : ℕ) then singularValues A i else 0 := by
  classical
  let U := (exists_isSVD A).choose
  let V := (exists_isSVD A).choose_spec.choose
  have h : IsSVD A U V := (exists_isSVD A).choose_spec.choose_spec
  let D : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
    Matrix.diagonal fun i => if (i : ℕ) < k then 0 else singularValues A i
  have hD : (rectDiag (fun i => if i < k then 0 else singularValues A i) :
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ) = D := by
    ext i j
    simp only [D, rectDiag_apply, Matrix.diagonal_apply, Fin.ext_iff]
  have hsplit : A = h.truncatedMatrix k + U * D * Vᴴ := by
    unfold IsSVD.truncatedMatrix
    simpa only [hD] using h.eq_head_add_tail k
  have herr : A - truncatedSVD A k = U * D * Vᴴ := by
    change A - h.truncatedMatrix k = _
    calc
      A - h.truncatedMatrix k =
          (h.truncatedMatrix k + U * D * Vᴴ) - h.truncatedMatrix k :=
        congrArg (fun X => X - h.truncatedMatrix k) hsplit
      _ = U * D * Vᴴ := by abel
  have hDp : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr fun i => by
    split_ifs
    · exact le_rfl
    · exact singularValues_nonneg A i
  have hinv : nuclearNorm (U * D * Vᴴ) = nuclearNorm D := by
    simpa only [schattenNormReal_one] using
      schattenNormReal_isometry_mul_mul_conjTranspose h.conjTranspose_mul_left
        h.conjTranspose_mul_right D 1
  rw [herr, hinv, nuclearNorm_eq_trace_of_posSemidef hDp]
  simp only [D, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hik : (i : ℕ) < k
  · simp only [if_pos hik, if_neg (not_le.mpr hik)]
  · simp only [if_neg hik, if_pos (not_lt.mp hik)]

/-- The optimal squared Frobenius tail of the PSD square root equals the nuclear tail of
the matrix itself. Both sides are the sum of its omitted nonnegative eigenvalues.
Martinsson–Tropp 2020, §14.2; adapted from frontend commit
`6a845a2ec27f37c1a98118c107a06a13ce45273d`, `Matrix/Functions/AbsoluteValue.lean`. -/
theorem bestRankFrobSq_sqrt_eq_nuclearNorm_sub_truncatedSVD {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (k : ℕ) :
    bestRankFrobSq (CFC.sqrt A) k = nuclearNorm (A - truncatedSVD A k) := by
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hGram : (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [hS, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have hσ (i : Fin (Fintype.card n)) :
      singularValues (CFC.sqrt A) i ^ 2 = singularValues A i := by
    have h := sq_singularValues_eq_eigenvalues₀ (CFC.sqrt A) i
    have he := congrFun (eigenvalues₀_eq_of_matrix_eq
      (Matrix.isHermitian_conjTranspose_mul_self (CFC.sqrt A)) hA.isHermitian hGram) i
    exact h.trans (he.trans (singularValues_eq_eigenvalues₀_of_posSemidef hA i).symm)
  rw [bestRankFrobSq, nuclearNorm_sub_truncatedSVD_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => if k ≤ i then singularValues (CFC.sqrt A) i ^ 2 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [hσ]

end NLAlib
