import NLAlib.Matrix.Spectral.SingularValueSpectrum
/-!
# Equal Gram matrices and singular values

Two matrices with the same column domain and the same actual Gram matrix have
the same native zero-padded singular values, even with different row spaces.
Source: Horn–Johnson (2013), §2.6; supports QR, absolute functional calculus and
invariant-norm spectral variation.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Equal Gram matrices have exactly equal native zero-padded singular values,
on arbitrary finite real matrix indices, with possibly different row types. -/
theorem toEuclideanLin_singularValues_eq_of_gram_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix p n ℝ) (hGram : Aᴴ * A = Bᴴ * B) (k : ℕ) :
    A.toEuclideanLin.singularValues k = B.toEuclideanLin.singularValues k := by
  by_cases hk : k < Fintype.card n
  · let i : Fin (Fintype.card n) := ⟨k, hk⟩
    have hA := sq_toEuclideanLin_singularValues_eq_eigenvalues₀ A i
    have hB := sq_toEuclideanLin_singularValues_eq_eigenvalues₀ B i
    have he := eigenvalues₀_eq_of_eq hGram
      (Matrix.isHermitian_conjTranspose_mul_self A) (Matrix.isHermitian_conjTranspose_mul_self B) i
    have hs : A.toEuclideanLin.singularValues k ^ 2 = B.toEuclideanLin.singularValues k ^ 2 :=
      hA.trans (he.trans hB.symm)
    nlinarith [LinearMap.singularValues_nonneg A.toEuclideanLin k,
      LinearMap.singularValues_nonneg B.toEuclideanLin k]
  · have hkn : Module.finrank ℝ (EuclideanSpace ℝ n) ≤ k := by
      simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk
    rw [LinearMap.singularValues_of_finrank_le _ hkn, LinearMap.singularValues_of_finrank_le _ hkn]

end NLAlib
