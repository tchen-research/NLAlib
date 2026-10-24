import NLAlib.Matrix.Spectral.SpectralGramFactor
import NLAlib.Matrix.Basic.MoorePenrose

/-!
# Positive adjugates and Gram-pseudoinverse cancellation

The adjugate of a PSD matrix is itself PSD, including at singular matrices:
factor the matrix as `Cᴴ C` and reverse the factors under the adjugate.
Gram kernel identities retain the possibly nonzero singular adjugate while
showing that its product with the data adjoint vanishes. The resulting
determinant-weighted pseudoinverse formula is valid at every rank.

Source: Dereziński–Warmuth 2018, Theorems 5–6 and Appendix B.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d] [DecidableEq d]

omit [Fintype n] in
/-- A PSD matrix has a PSD adjugate, including corank one, size one and
the empty size. The proof is the square-Gram factorization, rather than an
incorrect assumption that singular adjugates vanish. -/
theorem _root_.Matrix.PosSemidef.adjugate {A : Matrix d d 𝕜} (hA : A.PosSemidef) :
    A.adjugate.PosSemidef := by
  rw [← spectralGramRows_adjoint_mul hA, Matrix.adjugate_mul_distrib,
    ← Matrix.adjugate_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- A singular column Gram adjugate annihilates the actual data adjoint.
The adjugate may itself be nonzero. -/
theorem adjugate_gram_mul_conjTranspose_eq_zero (X : Matrix n d 𝕜)
    (hdet : (Xᴴ * X).det = 0) : (Xᴴ * X).adjugate * Xᴴ = 0 := by
  apply (Matrix.mul_conjTranspose_mul_self_eq_zero X (Xᴴ * X).adjugate).mp
  rw [Matrix.adjugate_mul, hdet, zero_smul]

omit [Fintype n] in
/-- At an invertible square matrix, determinant times the ordinary inverse
equals the adjugate. -/
theorem det_smul_inv_eq_adjugate {A : Matrix d d 𝕜} (hA : IsUnit A) :
    A.det • A⁻¹ = A.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul,
    mul_inv_cancel₀ ((Matrix.isUnit_iff_isUnit_det _).mp hA).ne_zero, one_smul]

omit [Fintype n] in
/-- The total determinant-weighted ordinary inverse is the adjugate minus its
singular contribution. This identity retains nonzero corank-one adjugates. -/
theorem det_smul_inv_eq_adjugate_sub_ite (A : Matrix d d 𝕜) :
    A.det • A⁻¹ = A.adjugate - if A.det = 0 then A.adjugate else 0 := by
  by_cases hdet : A.det = 0
  · simp [hdet]
  · have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    rw [det_smul_inv_eq_adjugate hA, if_neg hdet, sub_zero]

/-- The literal determinant-weighted Moore–Penrose inverse is the adjugate
Gram numerator at every rank, including singular subsets of zero sampling mass. -/
theorem adjugate_gram_mul_conjTranspose_eq_det_smul_moorePenroseInverse
    (X : Matrix n d 𝕜) :
    (Xᴴ * X).adjugate * Xᴴ = (Xᴴ * X).det • moorePenroseInverse X := by
  by_cases hdet : (Xᴴ * X).det = 0
  · rw [adjugate_gram_mul_conjTranspose_eq_zero X hdet, hdet, zero_smul]
  · have hG : IsUnit (Xᴴ * X) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    rw [moorePenroseInverse_eq_pinvL X hG, pinvL, ← Matrix.smul_mul,
      det_smul_inv_eq_adjugate hG]

end NLAlib
