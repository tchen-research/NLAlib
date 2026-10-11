import NLAlib.Matrix.InvariantNorm
import NLAlib.Matrix.RectangularDiagonalPermutation

/-!
# Every invariant norm is a singular-value gauge

Restriction to the injective rectangular diagonal gives an actual scalar norm.
Actual orthogonal matrices implement its signs/permutations, and the SVD proves
the representation on every matrix. Source: Bhatia (1997), Theorem IV.2.1.
Atlas: `unitarily-invariant-norm-def`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib
namespace OrthogonallyInvariantNorm

/-- Restrict a fixed-shape invariant matrix norm to its thin rectangular
diagonal. The permutation/sign symmetries are implemented by actual matrices. -/
def toSymmetricGaugeFin {m n : ℕ} (ν : OrthogonallyInvariantNorm (Fin m) (Fin n)) :
    SymmetricGauge (Fin (min m n)) where
  seminorm := ν.seminorm.comp (rectangularDiagonalLinear m n)
  eq_zero_of_map_eq_zero x hx := by
    have hD : rectangularDiagonal x = 0 := ν.eq_zero_of_map_eq_zero _ hx
    apply rectangularDiagonal_injective
    rw [hD]
    exact (map_zero (rectangularDiagonalLinear m n)).symm
  permutation_invariant x σ := by
    obtain ⟨U, V, hU, hV, hD⟩ := exists_orthogonal_rectangularDiagonal_perm x σ
    change ν.seminorm (rectangularDiagonal (x ∘ σ)) = ν.seminorm (rectangularDiagonal x)
    rw [← hD, ν.right_invariant _ V hV, ν.left_invariant _ U hU]
  sign_invariant x ε hε := by
    obtain ⟨U, hU, hD⟩ := exists_orthogonal_rectangularDiagonal_sign x ε hε
    change ν.seminorm (rectangularDiagonal (fun i => ε i * x i)) = ν.seminorm (rectangularDiagonal x)
    rw [← hD, ν.left_invariant _ U hU]

/-- The restricted gauge evaluates exactly to the original norm of the
fixed-shape rectangular diagonal, including signed vectors and empty shapes. -/
@[simp] theorem value_toSymmetricGaugeFin {m n : ℕ}
    (ν : OrthogonallyInvariantNorm (Fin m) (Fin n)) (x : Fin (min m n) → ℝ) :
    ν.toSymmetricGaugeFin.value x = ν.seminorm (rectangularDiagonal x) := rfl

/-- An invariant norm is exactly its restricted diagonal gauge evaluated on
the singular values. No norm representation hypothesis is assumed.
Bhatia (1997), Theorem IV.2.1. -/
theorem seminorm_eq_toSymmetricGaugeFin_singularValues {m n : ℕ}
    (ν : OrthogonallyInvariantNorm (Fin m) (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    ν.seminorm A = ν.toSymmetricGaugeFin.value (fun i : Fin (min m n) => singularValues A i) := by
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  have hU : HasOrthonormalCols U := hSVD.transpose_mul_left
  have hVt : HasOrthonormalCols Vᵀ := by
    change Vᵀᵀ * Vᵀ = 1
    rw [Matrix.transpose_transpose]
    exact hSVD.mul_transpose_right
  calc
    ν.seminorm A = ν.seminorm (U * rectDiag (singularValues A) * Vᵀ) := congrArg ν.seminorm hSVD.eq
    _ = ν.seminorm (rectDiag (singularValues A)) := by
      rw [ν.right_invariant _ Vᵀ hVt, ν.left_invariant _ U hU]
    _ = _ := by rw [value_toSymmetricGaugeFin, rectangularDiagonal_singularValues_eq_rectDiag]

/-- Relabel a bundled invariant norm, pulling it back through the exact matrix
linear equivalence. This preserves all norm properties and orthogonal symmetries. -/
def reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (ν : OrthogonallyInvariantNorm m n) (em : m ≃ p) (en : n ≃ q) : OrthogonallyInvariantNorm p q where
  seminorm := ν.seminorm.comp (Matrix.reindexLinearEquiv ℝ ℝ em.symm en.symm).toLinearMap
  eq_zero_of_map_eq_zero A hA := by
    have h := ν.eq_zero_of_map_eq_zero (A.reindex em.symm en.symm) hA
    ext i j
    have hh := congrArg (fun M : Matrix m n ℝ => M (em.symm i) (en.symm j)) h
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, Matrix.zero_apply] using hh
  left_invariant A U hU := by
    have hmul : (U * A).reindex em.symm en.symm =
        U.reindex em.symm em.symm * A.reindex em.symm en.symm := by
      simpa only [Matrix.reindex_apply, Equiv.symm_symm] using (Matrix.submatrix_mul_equiv U A em em en).symm
    change ν.seminorm ((U * A).reindex em.symm en.symm) = ν.seminorm (A.reindex em.symm en.symm)
    rw [hmul, ν.left_invariant _ _ (hU.reindex em.symm em.symm)]
  right_invariant A V hV := by
    have hmul : (A * V).reindex em.symm en.symm =
        A.reindex em.symm en.symm * V.reindex en.symm en.symm := by
      simpa only [Matrix.reindex_apply, Equiv.symm_symm] using (Matrix.submatrix_mul_equiv A V em en en).symm
    change ν.seminorm ((A * V).reindex em.symm en.symm) = ν.seminorm (A.reindex em.symm en.symm)
    rw [hmul, ν.right_invariant _ _ (hV.reindex en.symm en.symm)]

/-- The reindexed norm is the original norm of the inverse-reindexed matrix. -/
@[simp] theorem reindex_seminorm_apply {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (ν : OrthogonallyInvariantNorm m n) (em : m ≃ p) (en : n ≃ q) (A : Matrix p q ℝ) :
    (ν.reindex em en).seminorm A = ν.seminorm (A.reindex em.symm en.symm) := rfl

/-- The symmetric gauge associated to an arbitrary finite rectangular invariant
norm, obtained by restriction after finite-coordinate transport. -/
def toSymmetricGauge {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ν : OrthogonallyInvariantNorm m n) : SymmetricGauge (Fin (min (Fintype.card m) (Fintype.card n))) :=
  (ν.reindex (Fintype.equivFin m) (Fintype.equivFin n)).toSymmetricGaugeFin

/-- Every invariant norm has its actual symmetric-gauge representation on the
native singular-value vector, for arbitrary finite matrix indices.
Bhatia (1997), Theorem IV.2.1.
atlas: unitarily-invariant-norm-def (partial) -/
theorem seminorm_eq_toSymmetricGauge_matrixValue {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ν : OrthogonallyInvariantNorm m n) (A : Matrix m n ℝ) :
    ν.seminorm A = ν.toSymmetricGauge.matrixValue A := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  calc
    ν.seminorm A = (ν.reindex em en).seminorm (A.reindex em en) := by
      rw [reindex_seminorm_apply]
      congr 1
      ext i j
      simp [Matrix.reindex_apply]
    _ = (ν.reindex em en).toSymmetricGaugeFin.value
        (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues (A.reindex em en) i) :=
      seminorm_eq_toSymmetricGaugeFin_singularValues _ _
    _ = ν.toSymmetricGauge.matrixValue A := by
      apply congrArg (ν.reindex em en).toSymmetricGaugeFin.value
      funext i
      exact singularValues_reindex_eq_toEuclideanLin_singularValues A i

end OrthogonallyInvariantNorm

/-- Rectangular diagonal embedding on arbitrary finite matrix index types. Its
shape is the original matrix space, rather than an unrelated square thin space. -/
def rectangularDiagonalMatrix {m n : Type*} [Fintype m] [Fintype n]
    (x : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) : Matrix m n ℝ :=
  (rectangularDiagonal x).reindex (Fintype.equivFin m).symm (Fintype.equivFin n).symm

/-- The restricted gauge is exactly the original invariant norm of a signed
thin vector in the corresponding fixed-shape rectangular diagonal. -/
theorem OrthogonallyInvariantNorm.value_toSymmetricGauge {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ν : OrthogonallyInvariantNorm m n)
    (x : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) :
    ν.toSymmetricGauge.value x = ν.seminorm (rectangularDiagonalMatrix x) := rfl

end NLAlib
