import NLAlib.Matrix.Factorizations.QR
import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Perturbation.ConditionNumber

/-!
# Spectral consequences of QR over real or complex scalars

Orthonormal left multiplication preserves the Gram matrix, singular values and
Moore–Penrose condition number. These conditional identities need no QR existence
proof or recurrence, so they are available through the default import.
Sources: Trefethen–Bau, Theorem 7.1; Golub–Van Loan, Sections 2.6.2 and 5.2.
Atlas: `qr-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The zero-padded singular values of the triangular QR factor are exactly those of the
original matrix at every index, on arbitrary finite indices.
Trefethen--Bau, Theorem 7.1; Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem singularValues_eq_of_qr {A Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) :
    singularValues R = singularValues A := by
  funext k
  apply singularValues_eq_of_gram_eq R A
  exact conjTranspose_mul_self_eq_of_qr hQ hFactor

/-- QR preserves the total spectral condition number built from the
Moore--Penrose inverse, including singular and zero-rank matrices.
Golub--Van Loan, Section 2.6.2; supports `qr-decomposition`.
atlas: qr-decomposition (partial) -/
theorem moorePenroseConditionNumber_eq_of_qr [DecidableEq m] {A Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) : moorePenroseConditionNumber R = moorePenroseConditionNumber A := by
  rw [← hFactor, moorePenroseConditionNumber_mul_left_of_hasOrthonormalCols Q R hQ]

end NLAlib
