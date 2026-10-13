import NLAlib.Matrix.Basic.MoorePenrose
import NLAlib.Matrix.Subspaces.Projections

/-!
# Transformations of the Moore--Penrose inverse

Over `ℝ` or `ℂ` (`[RCLike 𝕜]`): scalar multiplication, nonsingular square matrices, Hermitian and
positive-semidefinite matrices, and left isometries (`HasOrthonormalCols`). The identities hold
at deficient and zero rank. Statements are written with `ᴴ` (F1); the Hermitian and
positive-semidefinite facts are in the `Matrix.IsHermitian` / `Matrix.PosSemidef` namespaces
(`hA.moorePenroseInverse`).
Source: Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def` and
`generalized-schur-complement-psd`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- Scaling the actual Moore--Penrose inverse by the inverse scalar: `(c A)⁺ = c⁻¹ A⁺`.
Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def`, including rank zero. -/
theorem moorePenroseInverse_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    moorePenroseInverse (c • A) = c⁻¹ • moorePenroseInverse A := by
  by_cases hc : c = 0
  · simp [hc]
  apply (isMoorePenroseInverse (c • A)).unique
  set B := moorePenroseInverse A
  have hAB : (c • A) * (c⁻¹ • B) = A * B := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hBA : (c⁻¹ • B) * (c • A) = B * A := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hAB, Matrix.mul_smul, mul_moorePenroseInverse_mul]
  · rw [hBA, Matrix.mul_smul, moorePenroseInverse_mul_moorePenroseInverse]
  · rw [hAB]
    exact mul_moorePenroseInverse_isHermitian A
  · rw [hBA]
    exact moorePenroseInverse_mul_isHermitian A

/-- On a nonsingular square matrix, the general inverse is the ordinary inverse.
Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def`. -/
theorem moorePenroseInverse_eq_inv_of_isUnit [DecidableEq n]
    (A : Matrix n n 𝕜) (hA : IsUnit A) : moorePenroseInverse A = A⁻¹ := by
  apply (isMoorePenroseInverse A).unique
  have hDet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor <;> simp [Matrix.mul_nonsing_inv _ hDet, Matrix.nonsing_inv_mul _ hDet]

/-- The general inverse of a Hermitian matrix is Hermitian.
Horn--Johnson 2013, Problem 7.3.P7; supports `generalized-schur-complement-psd`. -/
theorem _root_.Matrix.IsHermitian.moorePenroseInverse {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (NLAlib.moorePenroseInverse A).IsHermitian := by
  rw [Matrix.IsHermitian, ← moorePenroseInverse_conjTranspose, hA.eq]

/-- Deprecated alias (F1, transpose twins removed): use `Matrix.IsHermitian.moorePenroseInverse`. -/
@[deprecated (since := "2026-10-13")]
alias moorePenroseInverse_isSymm := Matrix.IsHermitian.moorePenroseInverse

/-- The general inverse of a left-isometric product is the reverse adjoint product:
`(Q A)⁺ = A⁺ Qᴴ` when `Qᴴ Q = 1`.
Horn--Johnson 2013, Problem 7.3.P7; supports `condition-number-def` for rectangular frames. -/
theorem moorePenroseInverse_mul_left_of_hasOrthonormalCols [DecidableEq m]
    (Q : Matrix p m 𝕜) (A : Matrix m n 𝕜) (hQ : HasOrthonormalCols Q) :
    moorePenroseInverse (Q * A) = moorePenroseInverse A * Qᴴ := by
  apply (isMoorePenroseInverse (Q * A)).unique
  have h := isMoorePenroseInverse A
  set B := moorePenroseInverse A
  have hQt : Qᴴ * Q = 1 := hQ.conjTranspose_mul_self
  have hBA : B * Qᴴ * (Q * A) = B * A := by
    calc
      B * Qᴴ * (Q * A) = B * (Qᴴ * Q) * A := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [hQt, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      Q * A * (B * Qᴴ) * (Q * A) = Q * (A * B * (Qᴴ * Q) * A) := by simp only [Matrix.mul_assoc]
      _ = Q * A := by rw [hQt, Matrix.mul_one, h.mul_mul_eq]
  · calc
      B * Qᴴ * (Q * A) * (B * Qᴴ) = (B * (Qᴴ * Q) * A * B) * Qᴴ := by
            simp only [Matrix.mul_assoc]
      _ = B * Qᴴ := by rw [hQt, Matrix.mul_one, h.inv_mul_inv_eq]
  · have he : Q * A * (B * Qᴴ) = Q * (A * B) * Qᴴ := by simp only [Matrix.mul_assoc]
    rw [he]
    calc
      (Q * (A * B) * Qᴴ)ᴴ = Q * (A * B)ᴴ * Qᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = Q * (A * B) * Qᴴ := by rw [h.conjTranspose_mul_eq]
  · rw [hBA]
    exact h.conjTranspose_inv_mul_eq

/-- Deprecated alias (F1, transpose twins removed): use
`moorePenroseInverse_mul_left_of_hasOrthonormalCols`. -/
@[deprecated (since := "2026-10-13")]
alias moorePenroseInverse_mul_left_eq_mul_conjTranspose :=
  moorePenroseInverse_mul_left_of_hasOrthonormalCols

/-- The actual Moore--Penrose inverse of a positive-semidefinite matrix
is positive semidefinite, including singular matrices. Horn--Johnson,
Section 7.3; supports `generalized-schur-complement-psd`. -/
theorem _root_.Matrix.PosSemidef.moorePenroseInverse [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) : (NLAlib.moorePenroseInverse A).PosSemidef := by
  have hB := hA.isHermitian.moorePenroseInverse
  have h := hA.mul_mul_conjTranspose_same (NLAlib.moorePenroseInverse A)
  simpa only [hB.eq, moorePenroseInverse_mul_moorePenroseInverse] using h

/-- Deprecated alias (F1, transpose twins removed): use `Matrix.PosSemidef.moorePenroseInverse`. -/
@[deprecated (since := "2026-10-13")]
alias moorePenroseInverse_posSemidef := Matrix.PosSemidef.moorePenroseInverse

end NLAlib
