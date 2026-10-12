import Mathlib.Analysis.Matrix.Spectrum

/-!
# Transport of Hermitian eigenvalue lists along matrix equality

Equality of matrices gives equality of their sorted spectral lists, independent
of the proofs of Hermitian symmetry. This is the basic transport interface
used in Gram decomposition and congruence arguments.
-/

noncomputable section

namespace NLAlib

/-- Equal Hermitian matrices have equal sorted eigenvalue lists.
Mathlib's spectral definition and proof irrelevance; helper for
`singular-value-interlacing` and congruence spectrum comparisons. -/
theorem eigenvalues₀_eq_of_matrix_eq {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [RCLike 𝕜] {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst B
  rfl

end NLAlib
