import NLAlib.Matrix.Spectral.SingularValueSpectrum
/-!
# Equal Gram matrices and singular values

Two matrices (over `ℝ` or `ℂ`) with the same column domain whose Gram matrices `AᴴA` have the
same characteristic polynomial (in particular, equal Gram matrices) have the same zero-padded
singular values, even with different row spaces.
Source: Horn–Johnson (2013), §2.6; supports QR, absolute functional calculus and
invariant-norm spectral variation.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

/-- Matrices with the same column type whose Gram matrices `AᴴA`, `BᴴB` have equal
characteristic polynomials have equal zero-padded singular values, with possibly different
row types. Horn–Johnson 2013, Section 2.6. -/
theorem singularValues_eq_of_gram_charpoly_eq (A : Matrix m n 𝕜) (B : Matrix p n 𝕜)
    (h : (Aᴴ * A).charpoly = (Bᴴ * B).charpoly) (k : ℕ) :
    singularValues A k = singularValues B k := by
  by_cases hk : k < Fintype.card n
  · have he := congrFun (eigenvalues₀_eq_of_charpoly_eq
      (Matrix.isHermitian_conjTranspose_mul_self A) (Matrix.isHermitian_conjTranspose_mul_self B)
      h) ⟨k, hk⟩
    have hs : singularValues A k ^ 2 = singularValues B k ^ 2 :=
      (sq_singularValues_eq_eigenvalues₀ A ⟨k, hk⟩).trans
        (he.trans (sq_singularValues_eq_eigenvalues₀ B ⟨k, hk⟩).symm)
    nlinarith [singularValues_nonneg A k, singularValues_nonneg B k]
  · have hkn : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) ≤ k := by
      simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk
    rw [singularValues_eq_linearMap, singularValues_eq_linearMap,
      LinearMap.singularValues_of_finrank_le _ hkn, LinearMap.singularValues_of_finrank_le _ hkn]

/-- Equal Gram matrices give exactly equal zero-padded singular values, on arbitrary finite
indices, with possibly different row types. Horn–Johnson 2013, Section 2.6. -/
theorem singularValues_eq_of_gram_eq (A : Matrix m n 𝕜) (B : Matrix p n 𝕜)
    (hGram : Aᴴ * A = Bᴴ * B) (k : ℕ) : singularValues A k = singularValues B k :=
  singularValues_eq_of_gram_charpoly_eq A B (congrArg Matrix.charpoly hGram) k

end NLAlib
