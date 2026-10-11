import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Matrix.SVD

/-!
# Diagonal polynomial filter envelopes

Entrywise bounds on rectangular diagonal and inverse diagonal filters imply exact
spectral norm envelopes. These convert the block polynomial-filter bound to its
scalar maximum/minimum form.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- A rectangular diagonal matrix has norm at most an entrywise absolute envelope.
Source: HMT (2011), §2.1; manuscript `sa:filter`, scalar filter envelope. -/
theorem specNorm_rectDiag_le {m n : ℕ} {s : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hs : ∀ i, i < min m n → |s i| ≤ b) :
    specNorm (rectDiag s : Matrix (Fin m) (Fin n) ℝ) ≤ b := by
  apply (sq_le_sq₀ (specNorm_nonneg _) hb).mp
  rw [specNorm_sq_eq_specNorm_transpose_mul_self, transpose_rectDiag_mul_rectDiag,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).2
  intro j
  simp only [Real.norm_eq_abs]
  split_ifs with hj
  · rw [abs_of_nonneg (sq_nonneg _)]
    have h := hs j (lt_min hj j.isLt)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).2 h
  · simpa using sq_nonneg b

/-- Filtering a rectangular diagonal by its right Gram evaluates the scalar filter
at its squared diagonal entries. Source: manuscript `sa:filter`, definition of `D`. -/
theorem rectDiag_mul_aeval_gram (s : ℕ → ℝ) (p : ℝ[X]) {m n : ℕ} :
    (rectDiag s : Matrix (Fin m) (Fin n) ℝ) *
      aeval ((rectDiag s : Matrix (Fin m) (Fin n) ℝ)ᵀ *
        (rectDiag s : Matrix (Fin m) (Fin n) ℝ)) p =
      rectDiag (fun i => s i * p.eval (s i ^ 2)) := by
  rw [transpose_rectDiag_mul_rectDiag, aeval_diagonal]
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [rectDiag_apply]
  by_cases hij : (i : ℕ) = j
  · simp [← hij, i.isLt]
  · simp only [if_neg hij, zero_mul]

/-- The leading polynomial diagonal has an explicit right inverse whose norm is at
most the reciprocal of any positive absolute lower envelope. Source: manuscript
`sa:filter`, `c_phi`; the actual minimum is a permitted choice of the envelope. -/
theorem diagonal_filter_right_inverse_and_specNorm_le {k : ℕ} (s : Fin k → ℝ)
    (p : ℝ[X]) {c : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval ((s i) ^ 2)|) :
    let C := aeval ((Matrix.diagonal s)ᵀ * Matrix.diagonal s) p
    let R := Matrix.diagonal (fun i => (p.eval ((s i) ^ 2))⁻¹)
    C * R = 1 ∧ specNorm R ≤ 1 / c := by
  dsimp only
  have hne : ∀ i, p.eval ((s i) ^ 2) ≠ 0 := by
    intro i hi
    have h := hmin i
    rw [hi, abs_zero] at h
    linarith
  constructor
  · rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, aeval_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa only [pow_two] using mul_inv_cancel₀ (hne i)
  · rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [Real.norm_eq_abs, abs_inv, ← one_div]
    exact one_div_le_one_div_of_le hc (hmin i)

end NLAlib
