import NLAlib.Krylov.Spectral.QRConvergence
import NLAlib.Matrix.Factorizations.Householder

/-!
# Convergence of the native unshifted QR process

The norm bounds imply convergence in the matrix topology. Signs are applied to
the actual accumulated factor, and the rank-unrestricted Householder routine
provides a concrete run. Source: Trefethen--Bau, Theorem 28.4.
-/

noncomputable section
open scoped Matrix Topology
open Filter
namespace NLAlib
variable {n : ℕ}

private theorem frobNorm_mul_sign_diagonal_sub_le
    (W Q : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) (hs : ∀ i, s i ^ 2 = 1) :
    frobNorm (W * Matrix.diagonal s - Q) ≤ frobNorm (W - Q * Matrix.diagonal s) := by
  have hDD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    nlinarith [hs i]
  have hD : HasOrthonormalCols (Matrix.diagonal s) := by
    change (Matrix.diagonal s)ᵀ * Matrix.diagonal s = 1
    rw [Matrix.diagonal_transpose]
    exact hDD
  have he : (W - Q * Matrix.diagonal s) * Matrix.diagonal s = W * Matrix.diagonal s - Q := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hDD, Matrix.mul_one]
  rw [← he]
  apply (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
  nlinarith [specNorm_le_one_of_orthonormal hD, frobNorm_nonneg (W - Q * Matrix.diagonal s)]

open scoped Matrix.Norms.Frobenius in
/-- The actual unshifted QR matrices converge to the ordered eigenvalue diagonal,
and actual accumulated factors converge to the given eigenvectors after signs.
The smallest eigenvalue may be zero; no invertibility of the full input is used.
atlas: qr-algorithm-convergence (partial) -/
theorem tendsto_qrAlgorithm_and_alignedQ
    {qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hA : A = Q * Matrix.diagonal d * Qᵀ)
    (hd : StrictAnti fun i => |d i|)
    (hminor : ∀ j (hj : j ≤ n), IsUnit (Qᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj)))
    (hqr : ∀ k, QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    Tendsto (qrAlgorithm qr (fun _ => 0) A) atTop (𝓝 (Matrix.diagonal d)) ∧
      ∃ s : ℕ → Fin n → ℝ, (∀ k i, s k i ^ 2 = 1) ∧
        Tendsto (fun k => qrAlgorithmQ qr (fun _ => 0) A k * Matrix.diagonal (s k)) atTop (𝓝 Q) := by
  have hAQ : A * Q = Q * Matrix.diagonal d := by
    rw [hA, Matrix.mul_assoc]
    change Q * Matrix.diagonal d * (Qᴴ * Q) = _
    rw [hQ.conjTranspose_mul_self, Matrix.mul_one]
  obtain ⟨hiter, s, hs, hframe⟩ := tendsto_frobNorm_qrAlgorithm_and_alignedQ hQ hAQ hd hminor hqr
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [← frobNorm_eq_norm] using hiter
  · refine ⟨s, hs, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
    have hz := squeeze_zero (fun k => frobNorm_nonneg
      (qrAlgorithmQ qr (fun _ => 0) A k * Matrix.diagonal (s k) - Q))
      (fun k => frobNorm_mul_sign_diagonal_sub_le _ _ _ (hs k)) hframe
    simpa only [← frobNorm_eq_norm] using hz

/-- Householder QR is a concrete native run to which the symmetric QR convergence
and sign-aligned eigenvector convergence theorem applies, including singular input.
atlas: qr-algorithm-convergence (partial) -/
theorem tendsto_qrAlgorithm_householder_and_alignedQ
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hA : A = Q * Matrix.diagonal d * Qᵀ)
    (hd : StrictAnti fun i => |d i|)
    (hminor : ∀ j (hj : j ≤ n), IsUnit (Qᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj))) :
    Tendsto (qrAlgorithm (fun M => (householderQ M, householderR M)) (fun _ => 0) A)
        atTop (𝓝 (Matrix.diagonal d)) ∧
      ∃ s : ℕ → Fin n → ℝ, (∀ k i, s k i ^ 2 = 1) ∧
        Tendsto (fun k => qrAlgorithmQ (fun M => (householderQ M, householderR M))
          (fun _ => 0) A k * Matrix.diagonal (s k)) atTop (𝓝 Q) := by
  apply tendsto_qrAlgorithm_and_alignedQ hQ hA hd hminor
  apply qrAlgorithmSucceeds_of_forall_isQR
  intro M
  simpa only [show (Fin.castLE (le_refl n) : Fin n → Fin n) = id from rfl,
    Matrix.submatrix_id_id] using isQR_householderQR M (le_refl n)

end NLAlib
