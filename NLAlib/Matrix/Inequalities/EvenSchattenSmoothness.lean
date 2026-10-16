import NLAlib.Matrix.Functions.TraceEvenSmoothness
import NLAlib.Matrix.Norms.SchattenEvenMoments
import NLAlib.Matrix.Spectral.Complexification
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Uniform smoothness for even Schatten moments

Hermitian dilation transfers the trace estimate to arbitrary complex
rectangular matrices. Exact Gram moments give the real case by complexification.
No nonempty, rank, positivity or nonsingularity assumptions are needed.
Source: Tropp (2022), Theorem 8.2 and §8.5.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem even_power_rpow_two_div {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (hr : 0 < r) :
    (x ^ (2 * r)) ^ (2 / ((2 * r : ℕ) : ℝ)) = x ^ 2 := by
  have hp : ((2 * r : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  rw [mul_div_cancel₀ 2 hp]
  exact Real.rpow_two x

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private theorem dilation_sub (A H : Matrix m n ℂ) : dilation (A - H) = dilation A - dilation H := by
  ext (i | i) (j | j) <;> simp [dilation, Matrix.conjTranspose_sub]

open scoped Matrix.Norms.L2Operator in
/-- Sharp even-moment Schatten smoothness for arbitrary complex rectangular
matrices, including empty dimensions. Source: Tropp (2022), Theorem 8.2 and §8.5.
atlas: schatten-even-moment-smoothness (partial) -/
theorem schattenNormReal_even_moment_smoothness_complex (A H : Matrix m n ℂ)
    {r : ℕ} (hr : 0 < r) :
    ((schattenNormReal (A + H) (2 * r : ℕ) ^ (2 * r) +
      schattenNormReal (A - H) (2 * r : ℕ) ^ (2 * r)) / 2) ^
        (2 / ((2 * r : ℕ) : ℝ)) ≤
      schattenNormReal A (2 * r : ℕ) ^ 2 +
        (((2 * r : ℕ) : ℝ) - 1) * schattenNormReal H (2 * r : ℕ) ^ 2 := by
  have hp : Even (2 * r) := even_two_mul r
  have h := re_trace_even_moment_smoothness (dilation A) (dilation H)
    (isHermitian_dilation A) (isHermitian_dilation H) hp (by omega)
  have ht (X : Matrix m n ℂ) : (dilation X ^ (2 * r)).trace.re =
      2 * schattenNormReal X (2 * r : ℕ) ^ (2 * r) := by
    exact re_trace_dilation_pow_even X hr
  rw [← dilation_add, ← dilation_sub, ht (A + H), ht (A - H), ht A, ht H] at h
  have hc : 0 < (2 : ℝ) ^ (2 / ((2 * r : ℕ) : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hplus := schattenNormReal_nonneg (A + H) ((2 * r : ℕ) : ℝ)
  have hminus := schattenNormReal_nonneg (A - H) ((2 * r : ℕ) : ℝ)
  have havg : 0 ≤ (schattenNormReal (A + H) (2 * r : ℕ) ^ (2 * r) +
      schattenNormReal (A - H) (2 * r : ℕ) ^ (2 * r)) / 2 :=
    div_nonneg (add_nonneg (pow_nonneg hplus _) (pow_nonneg hminus _)) (by norm_num)
  have hl :
      (2 * schattenNormReal (A + H) (2 * r : ℕ) ^ (2 * r) +
        2 * schattenNormReal (A - H) (2 * r : ℕ) ^ (2 * r)) / 2 =
      2 * ((schattenNormReal (A + H) (2 * r : ℕ) ^ (2 * r) +
        schattenNormReal (A - H) (2 * r : ℕ) ^ (2 * r)) / 2) := by ring
  rw [hl, Real.mul_rpow (by norm_num) havg,
    Real.mul_rpow (by norm_num) (pow_nonneg (schattenNormReal_nonneg A _) _),
    Real.mul_rpow (by norm_num) (pow_nonneg (schattenNormReal_nonneg H _) _),
    even_power_rpow_two_div (schattenNormReal_nonneg A _) hr,
    even_power_rpow_two_div (schattenNormReal_nonneg H _) hr] at h
  apply (mul_le_mul_iff_right₀ hc).mp
  convert! h using 1
  ring

open scoped Matrix.Norms.L2Operator in
/-- Complexification preserves every positive even Schatten norm, as follows
from equality of the actual Gram trace moments. -/
theorem schattenNormReal_complexification_even (A : Matrix m n ℝ) {r : ℕ} (hr : 0 < r) :
    schattenNormReal (A.map Complex.ofReal) (2 * r : ℕ) = schattenNormReal A (2 * r : ℕ) := by
  apply (pow_left_inj₀ (schattenNormReal_nonneg _ _) (schattenNormReal_nonneg _ _)
    (by omega : 2 * r ≠ 0)).mp
  rw [schattenNormReal_pow_even_eq_re_trace_gram _ hr,
    schattenNormReal_pow_even_eq_re_trace_gram _ hr]
  have hgram : (A.map Complex.ofReal)ᴴ * A.map Complex.ofReal =
      (realMatrixComplexification (Aᴴ * A) : Matrix n n ℂ) := by
    ext i j
    simp [Matrix.mul_apply, realMatrixComplexification_apply, Complex.ofReal_sum,
      Complex.ofReal_mul]
  rw [hgram, ← map_pow, realMatrixComplexification_apply]
  simp [Matrix.trace, RCLike.re_to_complex, RCLike.re_to_real]

open scoped Matrix.Norms.L2Operator in
/-- Sharp even-moment Schatten smoothness for arbitrary real rectangular
matrices, including empty dimensions. Source: Tropp (2022), Theorem 8.2 and §8.5.
atlas: schatten-even-moment-smoothness (partial) -/
theorem schattenNormReal_even_moment_smoothness_real (A H : Matrix m n ℝ)
    {r : ℕ} (hr : 0 < r) :
    ((schattenNormReal (A + H) (2 * r : ℕ) ^ (2 * r) +
      schattenNormReal (A - H) (2 * r : ℕ) ^ (2 * r)) / 2) ^
        (2 / ((2 * r : ℕ) : ℝ)) ≤
      schattenNormReal A (2 * r : ℕ) ^ 2 +
        (((2 * r : ℕ) : ℝ) - 1) * schattenNormReal H (2 * r : ℕ) ^ 2 := by
  have h := schattenNormReal_even_moment_smoothness_complex
    (A.map Complex.ofReal) (H.map Complex.ofReal) hr
  have hadd : A.map Complex.ofReal + H.map Complex.ofReal = (A + H).map Complex.ofReal := by
    ext i j; simp
  have hsub : A.map Complex.ofReal - H.map Complex.ofReal = (A - H).map Complex.ofReal := by
    ext i j; simp
  rw [hadd, hsub,
    schattenNormReal_complexification_even (A + H) hr,
    schattenNormReal_complexification_even (A - H) hr,
    schattenNormReal_complexification_even A hr,
    schattenNormReal_complexification_even H hr] at h
  exact h

end NLAlib
