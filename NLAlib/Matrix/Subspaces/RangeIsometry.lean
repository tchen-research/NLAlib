import NLAlib.Matrix.Subspaces.Projections

/-!
# Orthonormal coordinates preserve norms on their range

Multiplication by `Qᴴ` preserves the Frobenius and spectral norms of every matrix whose
columns lie in the range of an orthonormal frame `Q`. These range-based forms combine the
native projector and isometry APIs; in particular, they supply the arbitrary-residual clause
of atlas `sketched-regression`.

The scope was compared with `NLA-lib/NLAlib`, commit
`6a845a2ec27f37c1a98118c107a06a13ce45273d`, `Regression/SketchAndSolve.lean`.
The proofs below use the existing backend lemmas directly.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- Orthonormal coordinates preserve squared Frobenius norm for every matrix whose columns
lie in the frame's range. This applies to any residual, rather than only a chosen projection
residual; it supplies the range-isometry clause of `sketched-regression`. -/
theorem frobSq_conjTranspose_mul_of_range_le {Q : Matrix m n 𝕜} {E : Matrix m p 𝕜}
    (hQ : HasOrthonormalCols Q)
    (hE : LinearMap.range E.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    frobSq (Qᴴ * E) = frobSq E := by
  have h := mul_conjTranspose_mul_eq_of_range_le hQ hE
  calc
    frobSq (Qᴴ * E) = frobSq (Q * (Qᴴ * E)) :=
      (frobSq_mul_left_of_orthonormal hQ.conjTranspose_mul_self _).symm
    _ = frobSq E := congrArg frobSq h

/-- Orthonormal coordinates preserve Frobenius norm on the frame's range. This is the
arbitrary-residual Frobenius isometry used in `sketched-regression`.
atlas: sketched-regression (partial) -/
theorem frobNorm_conjTranspose_mul_of_range_le {Q : Matrix m n 𝕜} {E : Matrix m p 𝕜}
    (hQ : HasOrthonormalCols Q)
    (hE : LinearMap.range E.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    frobNorm (Qᴴ * E) = frobNorm E := by
  simp only [frobNorm, frobSq_conjTranspose_mul_of_range_le hQ hE]

/-- Orthonormal coordinates preserve spectral norm on the frame's range. This is the
arbitrary-residual spectral isometry used in `sketched-regression`.
atlas: sketched-regression (partial) -/
theorem specNorm_conjTranspose_mul_of_range_le [DecidableEq p]
    {Q : Matrix m n 𝕜} {E : Matrix m p 𝕜} (hQ : HasOrthonormalCols Q)
    (hE : LinearMap.range E.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    specNorm (Qᴴ * E) = specNorm E :=
  specNorm_conjTranspose_mul_of_eq_mul hQ.conjTranspose_mul_self
    (mul_conjTranspose_mul_eq_of_range_le hQ hE).symm

end NLAlib
