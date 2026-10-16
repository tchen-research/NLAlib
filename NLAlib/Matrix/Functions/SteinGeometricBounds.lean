import NLAlib.Matrix.Functions.SteinGramian

/-! # Geometric spectral and Frobenius error bounds for Stein Gramians -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]

private theorem specNorm_pow_le_pow {A : Matrix n n K} {q : ℝ} (hA : specNorm A ≤ q)
    (j : ℕ) : specNorm (A ^ j) ≤ q ^ j := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz : A ^ j = 0 := Subsingleton.elim _ _
    rw [hz, specNorm_zero]
    exact pow_nonneg ((specNorm_nonneg A).trans hA) j
  | inr hn =>
    simp only [specNorm_eq_norm] at *
    exact (norm_pow_le A j).trans (pow_le_pow_left₀ (norm_nonneg A) hA j)

private theorem specNorm_steinTerm_le {A Q : Matrix n n K} {q : ℝ} (hA : specNorm A ≤ q)
    (j : ℕ) : specNorm (A ^ j * Q * (Aᴴ) ^ j) ≤ (q ^ 2) ^ j * specNorm Q := by
  have hq : 0 ≤ q := (specNorm_nonneg A).trans hA
  rw [← Matrix.conjTranspose_pow]
  calc
    _ ≤ specNorm (A ^ j * Q) * specNorm (A ^ j)ᴴ := specNorm_mul_le _ _
    _ ≤ (q ^ j * specNorm Q) * q ^ j := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul
        ((specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (specNorm_pow_le_pow hA j) (specNorm_nonneg Q)))
        (specNorm_pow_le_pow hA j) (specNorm_nonneg _)
        (mul_nonneg (pow_nonneg hq _) (specNorm_nonneg Q))
    _ = _ := by rw [← pow_mul, mul_comm 2 j, pow_mul]; ring

private theorem frobNorm_steinTerm_le {A Q : Matrix n n K} {q : ℝ} (hA : specNorm A ≤ q)
    (j : ℕ) : frobNorm (A ^ j * Q * (Aᴴ) ^ j) ≤ (q ^ 2) ^ j * frobNorm Q := by
  have hq : 0 ≤ q := (specNorm_nonneg A).trans hA
  rw [← Matrix.conjTranspose_pow]
  calc
    _ ≤ frobNorm (A ^ j * Q) * specNorm (A ^ j)ᴴ := frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ (q ^ j * frobNorm Q) * q ^ j := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul
        ((frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans (mul_le_mul_of_nonneg_right
          (specNorm_pow_le_pow hA j) (frobNorm_nonneg Q)))
        (specNorm_pow_le_pow hA j) (specNorm_nonneg _)
        (mul_nonneg (pow_nonneg hq _) (frobNorm_nonneg Q))
    _ = _ := by rw [← pow_mul, mul_comm 2 j, pow_mul]; ring

/-- The full Gramian's spectral norm has the usual geometric-series bound. -/
theorem specNorm_steinGramian_le {A Q : Matrix n n K} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) : specNorm (steinGramian A Q) ≤ specNorm Q / (1 - q ^ 2) := by
  have hq0 := (specNorm_nonneg A).trans hA
  have hq2 : |q ^ 2| < 1 := by rw [abs_of_nonneg (sq_nonneg q)]; nlinarith
  have hgeo := (summable_geometric_of_abs_lt_one hq2).mul_right (specNorm Q)
  have hn : Summable (fun j : ℕ => specNorm (A ^ j * Q * (Aᴴ) ^ j)) :=
    Summable.of_nonneg_of_le (fun _ => specNorm_nonneg _) (fun j => specNorm_steinTerm_le hA j) hgeo
  have hnorm : Summable (fun j : ℕ => ‖A ^ j * Q * (Aᴴ) ^ j‖) := by simpa [specNorm_eq_norm] using hn
  rw [specNorm_eq_norm]
  calc
    _ ≤ ∑' j : ℕ, ‖A ^ j * Q * (Aᴴ) ^ j‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, (q ^ 2) ^ j * specNorm Q :=
      hnorm.tsum_le_tsum (by simpa [specNorm_eq_norm] using (fun j => specNorm_steinTerm_le (Q := Q) hA j)) hgeo
    _ = _ := by rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hq2]; ring

open scoped Matrix.Norms.Frobenius in
/-- The same geometric-series bound in Frobenius norm. -/
theorem frobNorm_steinGramian_le {A Q : Matrix n n K} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) : frobNorm (steinGramian A Q) ≤ frobNorm Q / (1 - q ^ 2) := by
  have hq0 := (specNorm_nonneg A).trans hA
  have hq2 : |q ^ 2| < 1 := by rw [abs_of_nonneg (sq_nonneg q)]; nlinarith
  have hgeo := (summable_geometric_of_abs_lt_one hq2).mul_right (frobNorm Q)
  have hn : Summable (fun j : ℕ => frobNorm (A ^ j * Q * (Aᴴ) ^ j)) :=
    Summable.of_nonneg_of_le (fun _ => frobNorm_nonneg _) (fun j => frobNorm_steinTerm_le hA j) hgeo
  have hnorm : Summable (fun j : ℕ => ‖A ^ j * Q * (Aᴴ) ^ j‖) := by simpa [frobNorm_eq_norm] using hn
  rw [frobNorm_eq_norm]
  calc
    _ ≤ ∑' j : ℕ, ‖A ^ j * Q * (Aᴴ) ^ j‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, (q ^ 2) ^ j * frobNorm Q :=
      hnorm.tsum_le_tsum (by simpa [frobNorm_eq_norm] using (fun j => frobNorm_steinTerm_le (Q := Q) hA j)) hgeo
    _ = _ := by rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hq2]; ring

/-- Spectral-norm error for the actual finite Gramian prefix.
Source: user derivations, equation (G5) and geometric bound.
atlas: stein-gramian-smith-doubling (partial) -/
theorem specNorm_steinGramian_sub_partialSum_le {A Q : Matrix n n K} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) (N : ℕ) :
    specNorm (steinGramian A Q - steinPartialSum A Q N) ≤
      q ^ (2 * N) * specNorm Q / (1 - q ^ 2) := by
  have hq0 := (specNorm_nonneg A).trans hA
  have hs := summable_stein_of_power_bound A Q 1 q zero_le_one hq0 hq
    (by simpa using specNorm_pow_le_pow hA)
  rw [steinGramian_sub_partialSum A Q hs N]
  calc
    _ ≤ (q ^ 2) ^ N * specNorm (steinGramian A Q) := specNorm_steinTerm_le hA N
    _ ≤ (q ^ 2) ^ N * (specNorm Q / (1 - q ^ 2)) :=
      mul_le_mul_of_nonneg_left (specNorm_steinGramian_le hA hq) (pow_nonneg (sq_nonneg _) _)
    _ = _ := by rw [← pow_mul]; ring

/-- Frobenius-norm error for the same actual finite Gramian prefix.
Source: user derivations, Stein Gramian geometric bound.
atlas: stein-gramian-smith-doubling (partial) -/
theorem frobNorm_steinGramian_sub_partialSum_le {A Q : Matrix n n K} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) (N : ℕ) :
    frobNorm (steinGramian A Q - steinPartialSum A Q N) ≤
      q ^ (2 * N) * frobNorm Q / (1 - q ^ 2) := by
  have hq0 := (specNorm_nonneg A).trans hA
  have hs := summable_stein_of_power_bound A Q 1 q zero_le_one hq0 hq
    (by simpa using specNorm_pow_le_pow hA)
  rw [steinGramian_sub_partialSum A Q hs N]
  calc
    _ ≤ (q ^ 2) ^ N * frobNorm (steinGramian A Q) := frobNorm_steinTerm_le hA N
    _ ≤ (q ^ 2) ^ N * (frobNorm Q / (1 - q ^ 2)) :=
      mul_le_mul_of_nonneg_left (frobNorm_steinGramian_le hA hq) (pow_nonneg (sq_nonneg _) _)
    _ = _ := by rw [← pow_mul]; ring

end NLAlib
