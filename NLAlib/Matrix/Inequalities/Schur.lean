import NLAlib.Matrix.Inequalities.MajorizationHLP
import NLAlib.Matrix.Functions.PolynomialCalculus
import NLAlib.Matrix.Functions.CFCTrace
/-!
# Schur diagonal majorization and Peierls inequality

The squares of entries of the actual orthogonal eigenbasis form a doubly
stochastic map from the spectrum to the diagonal. No doubly stochastic matrix
is asserted to be orthostochastic in the converse direction.
Source: Horn–Johnson (2013), Theorem 4.3.45; Marshall–Olkin–Arnold (2011), 9.B.1.
Atlas: `schur-horn`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- Entrywise squared coordinates of an orthogonal matrix form a doubly
stochastic matrix. Schur's actual spectral-coordinate transport. -/
theorem sq_entries_mem_doublyStochastic {P : Matrix n n ℝ} (hP : HasOrthonormalCols P) :
    (Matrix.of fun i j => P i j ^ 2) ∈ doublyStochastic ℝ n := by
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp hP
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrArg (fun M : Matrix n n ℝ => M i i) hPP
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ite_true,
      Matrix.of_apply, pow_two] using h
  · intro j
    have h := congrArg (fun M : Matrix n n ℝ => M j j) hP.transpose_mul_self
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ite_true,
      Matrix.of_apply, pow_two] using h

/-- Every diagonal entry is an actual doubly stochastic weighted average of
the eigenvalues in the orthogonal spectral basis. -/
theorem diagonal_eq_sq_eigenvectorUnitary_mulVec (hA : A.IsHermitian) :
    Matrix.diag A = (Matrix.of fun i j => (hA.eigenvectorUnitary : Matrix n n ℝ) i j ^ 2) *ᵥ hA.eigenvalues := by
  funext i
  conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_apply, Matrix.mul_diagonal]
  ring

/-- A real symmetric matrix's diagonal is majorized by its spectrum. The
spectrum uses the matrix index enumeration, and `Majorized` sorts intrinsically.
Horn–Johnson (2013), Theorem 4.3.45; includes empty shapes.
atlas: schur-horn (partial) -/
theorem majorized_diagonal_eigenvalues (hA : A.IsHermitian) :
    Majorized (Matrix.diag A) hA.eigenvalues := by
  rw [diagonal_eq_sq_eigenvectorUnitary_mulVec hA]
  exact majorized_mulVec_of_doublyStochastic hA.eigenvalues
    (sq_entries_mem_doublyStochastic (transpose_eigenvectorUnitary_mul_self hA))

/-- Peierls' convex diagonal inequality, for every real convex scalar function
on the finite spectrum, with no extra integrability or smoothness hypothesis.
Horn–Johnson (2013), Theorem 4.3.45; Marshall–Olkin–Arnold (2011), 9.B.1.
atlas: schur-horn (partial) -/
theorem sum_convex_diagonal_le_trace_cfc (hA : A.IsHermitian) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) : (∑ i, φ (A i i)) ≤ (cfc φ A).trace := by
  rw [trace_cfc_eq_sum_eigenvalues hA φ]
  exact (majorized_diagonal_eigenvalues hA).sum_convex_le hφ

end NLAlib
