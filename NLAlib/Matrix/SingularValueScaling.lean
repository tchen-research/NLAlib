import NLAlib.Matrix.SpectralBounds

/-!
# Scaling singular values

Absolute homogeneity, including zero scalars and empty matrix dimensions.
Source: Horn–Johnson (2013), §2.6; helpers for the Ky Fan and Schatten norm APIs.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Negation leaves every zero-padded singular value unchanged. -/
theorem singularValues_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    singularValues (-A) = singularValues A := by
  have hP : (-1 : Matrix (Fin m) (Fin m) ℝ)ᵀ * (-1) = 1 := by simp
  simpa using singularValues_orthogonal_mul A hP

/-- Scaling a rectangular diagonal scales the represented sequence. -/
theorem rectDiag_smul {m n : ℕ} (c : ℝ) (a : ℕ → ℝ) :
    (rectDiag (c • a) : Matrix (Fin m) (Fin n) ℝ) = c • rectDiag a := by
  ext i j
  simp only [rectDiag_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split <;> simp_all

/-- Nonnegative scaling scales every zero-padded singular value, with no
nonzero or rank assumption. Source: uniqueness of the real SVD. -/
theorem singularValues_smul_of_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : singularValues (c • A) k = c * singularValues A k := by
  by_cases hk : k < min m n
  · obtain ⟨U, V, hSVD⟩ := exists_isSVD A
    have hfact : c • A = U *
        (rectDiag (c • singularValues A) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
      rw [rectDiag_smul, Matrix.mul_smul, Matrix.smul_mul]
      exact congrArg (fun B => c • B) hSVD.eq
    exact singularValues_eq_of_eq_mul_rectDiag_mul hSVD.transpose_mul_left
      hSVD.transpose_mul_right (fun i => mul_nonneg hc (singularValues_nonneg A i))
      (fun i j hij => mul_le_mul_of_nonneg_left (singularValues_antitone A hij) hc) hfact hk
  · rw [singularValues_eq_zero_of_min_le _ (by omega),
      singularValues_eq_zero_of_min_le A (by omega), mul_zero]

/-- Singular values are absolutely homogeneous over real scalars, including
zero scalars, zero ranks and empty dimensions. Horn–Johnson (2013), §2.6. -/
theorem singularValues_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) (k : ℕ) :
    singularValues (c • A) k = |c| * singularValues A k := by
  by_cases hc : 0 ≤ c
  · rw [singularValues_smul_of_nonneg A hc, abs_of_nonneg hc]
  · have hc : c < 0 := lt_of_not_ge hc
    have hfact : c • A = -((-c) • A) := by simp
    rw [hfact, singularValues_neg, singularValues_smul_of_nonneg A (by linarith), abs_of_neg hc]

end NLAlib
