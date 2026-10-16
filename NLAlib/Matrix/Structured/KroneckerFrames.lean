import NLAlib.Matrix.Structured.KroneckerSpectrum
import NLAlib.Matrix.Spectral.ThinSingularFunctions
import NLAlib.ForMathlib.Analysis.FinitePairNorm

/-! # Kronecker products in thin singular frames

The tensor factorization does not require ordered intermediate diagonal
coefficients. It gives the exact real or complex spectral norm, including
arbitrary rectangular shapes and empty singular blocks.
Source: Horn–Johnson (1991), Theorem 4.2.15.
-/
noncomputable section
open scoped Matrix Kronecker
namespace NLAlib
variable {𝕜 m n p q r s : Type*} [RCLike 𝕜]
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r] [Fintype s]
variable [DecidableEq r] [DecidableEq s]

omit [Fintype m] [Fintype n] [Fintype p] [Fintype q] in
/-- Tensoring two real-diagonal thin factorizations multiplies their coefficients. -/
theorem thinSingularMatrix_kronecker (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (P : Matrix p s 𝕜) (Q : Matrix q s 𝕜) (f : r → ℝ) (g : s → ℝ) :
    thinSingularMatrix U V f ⊗ₖ thinSingularMatrix P Q g =
      thinSingularMatrix (U ⊗ₖ P) (V ⊗ₖ Q) (fun ij => f ij.1 * g ij.2) := by
  simp only [thinSingularMatrix, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal, Matrix.conjTranspose_kronecker, RCLike.ofReal_mul]

open scoped Matrix.Norms.L2Operator in
/-- Thin singular factorizations prove exact spectral-norm multiplication,
uniformly over the real and complex numbers. -/
theorem specNorm_kronecker_of_thinSVD [DecidableEq m] [DecidableEq n]
    [DecidableEq p] [DecidableEq q] {A : Matrix m n 𝕜} {B : Matrix p q 𝕜}
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {P : Matrix p s 𝕜} {Q : Matrix q s 𝕜}
    {f : r → ℝ} {g : s → ℝ} (hA : IsThinSVD A U V f) (hB : IsThinSVD B P Q g) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B := by
  have hAf : A = thinSingularMatrix U V f := hA.eq
  have hBg : B = thinSingularMatrix P Q g := hB.eq
  rw [hAf, hBg, thinSingularMatrix_kronecker,
    specNorm_thinSingularMatrix _ _ (hasOrthonormalCols_kronecker hA.left_orth hB.left_orth)
      (hasOrthonormalCols_kronecker hA.right_orth hB.right_orth), norm_pair_mul,
    specNorm_thinSingularMatrix U V hA.left_orth hA.right_orth,
    specNorm_thinSingularMatrix P Q hB.left_orth hB.right_orth]

end NLAlib
