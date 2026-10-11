import NLAlib.Matrix.Norms

/-!
# Complex Frobenius identities

Uses Mathlib's scoped Frobenius norm, and connects the real squared norm to
NLAlib's established `frobSq`. Sources: operator re-derivation `sa:amm`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.Frobenius
namespace NLAlib

/-- The squared Frobenius norm is the sum of squared norms of the entries.
Source: the Frobenius definition, supporting operator re-derivation `sa:amm`. -/
theorem frobenius_norm_sq_eq_sum_norm_sq {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup 𝕜] (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Mathlib's real Frobenius norm squared equals the library's `frobSq`.
Source: the Frobenius definition, supporting operator re-derivation `sa:amm`. -/
theorem frobenius_norm_sq_eq_frobSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ‖A‖ ^ 2 = frobSq A := by
  rw [frobenius_norm_sq_eq_sum_norm_sq, frobSq_eq_sum_sq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- A complex outer product has Frobenius norm squared equal to the product of
the two squared Euclidean norms. Source: operator re-derivation `sa:amm-variance`. -/
theorem frobenius_norm_sq_vecMulVec {m n : Type*} [Fintype m] [Fintype n]
    (a : m → ℂ) (b : n → ℂ) :
    ‖Matrix.vecMulVec a b‖ ^ 2 = (∑ i, ‖a i‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_norm_sq, Finset.sum_mul_sum]
  simp only [Matrix.vecMulVec_apply, norm_mul, mul_pow]

/-- Embedding a real matrix into complex entries identifies its complex
Frobenius norm squared with `frobSq`. Source: operator re-derivation `sa:amm`. -/
theorem frobenius_norm_sq_map_ofReal_eq_frobSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ‖A.map Complex.ofReal‖ ^ 2 = frobSq A := by
  rw [frobenius_norm_sq_eq_sum_norm_sq, frobSq_eq_sum_sq]
  simp only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end NLAlib
