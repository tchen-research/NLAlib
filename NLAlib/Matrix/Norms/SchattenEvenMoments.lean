import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Spectral.GramSpectralSums
import NLAlib.Matrix.Functions.HermitianCalculus

/-! # Even Schatten moments and Hermitian dilation

Exact moment identities over either scalar field, with arbitrary finite
rectangular shapes and no nonempty or rank hypotheses.
Source: Tropp 2022, Section 8.5; `schatten-even-moment-smoothness`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

private theorem re_trace_pow_eq_eigenvalue_sum (A : Matrix n n 𝕜)
    (hA : A.IsHermitian) (r : ℕ) :
    RCLike.re (A ^ r).trace = ∑ i, hA.eigenvalues i ^ r := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [map_sum, Pi.pow_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

open scoped Matrix.Norms.L2Operator in
/-- An even Schatten power is exactly its column-Gram trace moment.
atlas: schatten-even-moment-smoothness (partial) -/
theorem schattenNormReal_pow_even_eq_re_trace_gram (A : Matrix m n 𝕜)
    {r : ℕ} (hr : 0 < r) :
    schattenNormReal A (2 * r : ℕ) ^ (2 * r) = RCLike.re ((Aᴴ * A) ^ r).trace := by
  have hp : (0 : ℝ) < (2 * r : ℕ) := by positivity
  have hsum : 0 ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i ^ ((2 * r : ℕ) : ℝ) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) _
  rw [schattenNormReal, ← Real.rpow_natCast, one_div,
    Real.rpow_inv_rpow hsum hp.ne']
  rw [re_trace_pow_eq_eigenvalue_sum _ (Matrix.isHermitian_conjTranspose_mul_self A),
    sum_eigenvalues_gram_eq_sum_singularValues A (fun x => x ^ r)]
  simp only [← pow_mul, Real.rpow_natCast]
  symm
  exact sum_range_singularValues_map_eq_of_min_le A (fun x => x ^ (2 * r))
    (by simp [show 2 * r ≠ 0 by omega]) (min_le_right _ _)

open scoped Matrix.Norms.L2Operator in
/-- For a Hermitian matrix its even Schatten power is its ordinary trace power.
atlas: schatten-even-moment-smoothness (partial) -/
theorem schattenNormReal_pow_even_eq_re_trace (A : Matrix n n 𝕜)
    (hA : A.IsHermitian) {r : ℕ} (hr : 0 < r) :
    schattenNormReal A (2 * r : ℕ) ^ (2 * r) = RCLike.re (A ^ (2 * r)).trace := by
  rw [schattenNormReal_pow_even_eq_re_trace_gram A hr,
    hA.eq, ← pow_two, ← pow_mul]

/-- The even power of a rectangular Hermitian dilation is the block sum
of its row- and column-Gram powers. -/
theorem dilation_pow_even (A : Matrix m n 𝕜) (r : ℕ) :
    dilation A ^ (2 * r) = Matrix.fromBlocks ((A * Aᴴ) ^ r) 0 0 ((Aᴴ * A) ^ r) := by
  rw [pow_mul, dilation_sq, Matrix.fromBlocks_diagonal_pow]

open scoped Matrix.Norms.L2Operator in
/-- Hermitian dilation doubles every positive even Schatten moment exactly,
including empty rectangular dimensions.
atlas: schatten-even-moment-smoothness (partial) -/
theorem re_trace_dilation_pow_even (A : Matrix m n 𝕜) {r : ℕ} (hr : 0 < r) :
    RCLike.re (dilation A ^ (2 * r)).trace =
      2 * schattenNormReal A (2 * r : ℕ) ^ (2 * r) := by
  rw [dilation_pow_even]
  have htrace : (Matrix.fromBlocks ((A * Aᴴ) ^ r) 0 0 ((Aᴴ * A) ^ r)).trace =
      ((A * Aᴴ) ^ r).trace + ((Aᴴ * A) ^ r).trace := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [htrace, map_add,
    re_trace_pow_eq_eigenvalue_sum _ (Matrix.isHermitian_mul_conjTranspose_self A),
    re_trace_pow_eq_eigenvalue_sum _ (Matrix.isHermitian_conjTranspose_mul_self A),
    sum_eigenvalues_mul_adjoint_eq_adjoint_mul A (fun x => x ^ r) (by simp [hr.ne'])]
  rw [schattenNormReal_pow_even_eq_re_trace_gram A hr,
    re_trace_pow_eq_eigenvalue_sum _ (Matrix.isHermitian_conjTranspose_mul_self A)]
  ring

end NLAlib
