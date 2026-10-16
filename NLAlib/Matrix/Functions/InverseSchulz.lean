import NLAlib.Matrix.Spectral.MatrixPowerConvergence
import NLAlib.Matrix.Norms.Core

/-!
# Newton–Schulz inverse refinement

The actual recursion squares its right residual, without a commutation
assumption on the starting matrix. Spectral-radius decay implies
invertibility and convergence; a spectral-norm estimate gives the explicit
quadratic rate. Higham (2008), §5.3. Atlas: `matrix-inverse-newton-schulz`.
-/

noncomputable section
open Filter
open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact Newton–Schulz refinement, starting from the supplied matrix.
The recursion is total, including singular inputs. -/
def inverseSchulzIterate (A X : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => X
  | k + 1 => inverseSchulzIterate A X k * (2 • 1 - A * inverseSchulzIterate A X k)

/-- A Newton–Schulz step squares the right residual, for arbitrary matrices. -/
theorem one_sub_mul_inverseSchulz_step (A X : Matrix n n ℂ) :
    1 - A * (X * (2 • 1 - A * X)) = (1 - A * X) ^ 2 := by
  simp only [two_smul]
  noncomm_ring

/-- The exact residual after `k` steps is the initial residual raised to `2^k`.
Higham (2008), §5.3; no initial commutation hypothesis is needed.
atlas: matrix-inverse-newton-schulz (partial) -/
theorem one_sub_mul_inverseSchulzIterate (A X : Matrix n n ℂ) (k : ℕ) :
    1 - A * inverseSchulzIterate A X k = (1 - A * X) ^ (2 ^ k) := by
  induction k with
  | zero => simp [inverseSchulzIterate]
  | succ k ih =>
    rw [inverseSchulzIterate, one_sub_mul_inverseSchulz_step, ih,
      ← pow_mul, pow_succ]

/-- A right residual of spectral radius below one forces the matrix to be
invertible, even when the initial approximate inverse does not commute.
atlas: matrix-inverse-newton-schulz (partial) -/
theorem isUnit_of_spectralRadius_inverseSchulz_residual_lt_one
    {A X : Matrix n n ℂ} (h : spectralRadius ℂ (1 - A * X) < 1) : IsUnit A := by
  have hAX : IsUnit (A * X) := by
    simpa only [sub_sub_cancel] using
      isUnit_one_sub_of_matrix_spectralRadius_lt_one h
  apply A.isUnit_iff_isUnit_det.mpr
  have hd := (A * X).isUnit_iff_isUnit_det.mp hAX
  rw [Matrix.det_mul] at hd
  exact isUnit_of_mul_isUnit_left hd

/-- The iterate error is the inverse times the negative right residual. -/
theorem inverseSchulzIterate_sub_inv {A X : Matrix n n ℂ}
    (hA : IsUnit A) (k : ℕ) :
    inverseSchulzIterate A X k - A⁻¹ = -A⁻¹ * (1 - A * X) ^ (2 ^ k) := by
  rw [← one_sub_mul_inverseSchulzIterate]
  have hi := Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp hA)
  calc
    _ = A⁻¹ * (A * inverseSchulzIterate A X k) - A⁻¹ := by
      rw [← Matrix.mul_assoc, hi, one_mul]
    _ = _ := by noncomm_ring

/-- Spectral-radius decay of the initial residual implies convergence of
the actual Newton–Schulz recursion to the matrix inverse.
atlas: matrix-inverse-newton-schulz (partial) -/
theorem tendsto_inverseSchulzIterate_inv {A X : Matrix n n ℂ}
    (h : spectralRadius ℂ (1 - A * X) < 1) :
    Tendsto (inverseSchulzIterate A X) atTop (𝓝 A⁻¹) := by
  have hA := isUnit_of_spectralRadius_inverseSchulz_residual_lt_one h
  have hpow := (tendsto_matrix_pow_zero_of_spectralRadius_lt_one h).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have ht := hpow.const_mul (-A⁻¹)
  have he : inverseSchulzIterate A X =
      fun k => -A⁻¹ * (1 - A * X) ^ (2 ^ k) + A⁻¹ := by
    funext k
    rw [← inverseSchulzIterate_sub_inv hA k, sub_add_cancel]
  rw [he]
  simpa using ht.add_const A⁻¹

/-- A spectral-norm contraction of the initial residual gives the explicit
Newton–Schulz error bound. Higham (2008), §5.3.
atlas: matrix-inverse-newton-schulz (partial) -/
theorem specNorm_inverseSchulzIterate_sub_inv_le [Nonempty n] {A X : Matrix n n ℂ}
    (hA : IsUnit A) (k : ℕ) :
    specNorm (inverseSchulzIterate A X k - A⁻¹) ≤
      specNorm A⁻¹ * specNorm (1 - A * X) ^ (2 ^ k) := by
  rw [inverseSchulzIterate_sub_inv hA]
  calc
    _ ≤ specNorm (-A⁻¹) * specNorm ((1 - A * X) ^ (2 ^ k)) := specNorm_mul_le _ _
    _ ≤ _ := by
      rw [specNorm_neg]
      exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (specNorm_nonneg _)

end NLAlib
