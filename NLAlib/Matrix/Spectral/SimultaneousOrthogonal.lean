import NLAlib.Matrix.Spectral.SimultaneousDiagonalization
import NLAlib.Matrix.Factorizations.PolarIntertwining
import NLAlib.Matrix.Functions.PolynomialCalculus
/-!
# Simultaneous orthogonal diagonalization of real symmetric families

A common eigenvector matrix is converted to its polar orthogonal factor.
The same factor works for an arbitrary, possibly infinite or empty, family.
Source: Horn--Johnson (2013), Theorem 2.5.5; supports
`simultaneous-diagonalization` and `simultaneous-diagonalization-congruence`.
-/

noncomputable section
open Matrix
namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- Every real symmetric matrix is diagonalizable over the real field.
Horn--Johnson (2013), Theorem 4.1.5; helper for simultaneous congruence. -/
theorem isDiagonalizable_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    IsDiagonalizable A := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hUt : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA
  have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_left_inverse hUt)
  refine ⟨U, hA.eigenvalues, hU, ?_⟩
  calc
    A * U = (U * diagonal hA.eigenvalues * Uᵀ) * U :=
      congrArg (fun M => M * U) (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA)
    _ = U * diagonal hA.eigenvalues := by rw [Matrix.mul_assoc, hUt, Matrix.mul_one]

/-- An arbitrary commuting family of real symmetric matrices has one common
orthogonal eigenvector matrix. Empty dimensions and empty families are included.
Horn--Johnson (2013), Theorem 2.5.5.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_orthogonal_diagonalization_of_commute
    (A : ι → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ (U : Matrix n n ℝ) (d : ι → n → ℝ), HasOrthonormalCols U ∧
      ∀ i, A i * U = U * diagonal (d i) := by
  obtain ⟨V, d, hV, hAV⟩ := exists_simultaneous_diagonalization_of_commute A
    (fun i => isDiagonalizable_of_isHermitian (hA i)) hcomm
  have hGram : IsUnit (Vᵀ * V) := ((Matrix.isUnit_transpose V).mpr hV).mul hV
  refine ⟨polarFrame V, d, hasOrthonormalCols_polarFrame V hGram, fun i => ?_⟩
  apply mul_polarFrame_eq_polarFrame_mul_of_intertwining (A i) (diagonal (d i)) V hGram
    (hAV i)
  have ht : (A i)ᵀ = A i := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hA i).eq
  simpa only [diagonal_transpose, ht] using hAV i

/-- Two commuting real symmetric matrices share an orthogonal basis in which
both congruences are diagonal. Horn--Johnson (2013), Theorem 2.5.5;
helper for `simultaneous-diagonalization-congruence`. -/
theorem exists_orthogonal_congruence_diagonal_of_commute {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ (U : Matrix n n ℝ) (a b : n → ℝ), HasOrthonormalCols U ∧
      Uᵀ * A * U = diagonal a ∧ Uᵀ * B * U = diagonal b := by
  let F : Bool → Matrix n n ℝ := fun i => if i then A else B
  have hF : ∀ i, (F i).IsHermitian := by intro i; cases i <;> assumption
  have hComm : Pairwise fun i j => Commute (F i) (F j) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hAB.symm
    · exact hAB
    · exact (hij rfl).elim
  obtain ⟨U, d, hU, hUF⟩ :=
    exists_simultaneous_orthogonal_diagonalization_of_commute F hF hComm
  refine ⟨U, d true, d false, hU, ?_, ?_⟩
  · rw [Matrix.mul_assoc, show A * U = U * diagonal (d true) from hUF true,
      ← Matrix.mul_assoc, (show Uᵀ * U = 1 from hU), Matrix.one_mul]
  · rw [Matrix.mul_assoc, show B * U = U * diagonal (d false) from hUF false,
      ← Matrix.mul_assoc, (show Uᵀ * U = 1 from hU), Matrix.one_mul]

end NLAlib
