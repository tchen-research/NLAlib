import NLAlib.Matrix.HadamardPowerSeries

/-!
# Monotonicity of natural Hadamard powers and exponential

Schur order multiplication and positive series coefficients preserve the
PSD order. Source: Horn--Johnson (2013), Section 7.5;
supports `schur-product-inequalities` and finite exponential certificates.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- Every natural entrywise power preserves Loewner order between PSD
matrices. Exponent zero is the identical all-ones matrix on both sides.
Horn--Johnson (2013), Section 7.5; helper for exponential strictness. -/
theorem map_pow_le_map_pow_of_posSemidef_le {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBA : B ≤ A) (k : ℕ) :
    B.map (fun t => t ^ k) ≤ A.map (fun t => t ^ k) := by
  have hA : A.PosSemidef := (hB.nonneg.trans hBA).posSemidef
  induction k with
  | zero =>
    have he : B.map (fun t => t ^ 0) = A.map (fun t => t ^ 0) := by ext i j; simp
    rw [he]
  | succ k ih =>
    have he (M : Matrix n n ℝ) : M.map (fun t => t ^ (k + 1)) = M.map (fun t => t ^ k) ⊙ M := by
      ext i j
      simp only [Matrix.map_apply, Matrix.hadamard_apply, pow_succ]
    rw [he, he]
    calc
      B.map (fun t => t ^ k) ⊙ B ≤ A.map (fun t => t ^ k) ⊙ B := by
        simpa only [Matrix.hadamard_comm] using hadamard_le_hadamard_of_posSemidef_left hB ih
      _ ≤ _ := hadamard_le_hadamard_of_posSemidef_left (posSemidef_map_pow hA k) hBA

/-- Finite exponential truncations preserve PSD order.
Horn--Johnson (2013), Section 7.5; helper for finite positivity certificates. -/
theorem sum_inv_factorial_smul_map_pow_le_of_posSemidef_le {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBA : B ≤ A) (N : ℕ) :
    (∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • B.map (fun t => t ^ k)) ≤
      ∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k) := by
  apply Finset.sum_le_sum
  intro k _
  exact smul_le_smul_of_nonneg_left (map_pow_le_map_pow_of_posSemidef_le hB hBA k) (by positivity)

/-- Entrywise exponential preserves Loewner order between PSD matrices.
This is order on quadratic forms, even when scalar entries are negative.
Horn--Johnson (2013), Section 7.5; helper for exponential strictness. -/
theorem map_exp_le_map_exp_of_posSemidef_le {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBA : B ≤ A) : B.map Real.exp ≤ A.map Real.exp := by
  have hsum := (hasSum_inv_factorial_smul_map_pow A).sub (hasSum_inv_factorial_smul_map_pow B)
  apply posSemidef_of_hasSum _ hsum
  intro k
  rw [← smul_sub]
  exact (Matrix.le_iff.mp (map_pow_le_map_pow_of_posSemidef_le hB hBA k)).smul (by positivity)

end NLAlib
