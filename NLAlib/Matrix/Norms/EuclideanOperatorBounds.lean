import NLAlib.Matrix.Spectral.SpectralBounds
/-!
# Euclidean vector bounds and matrix operator norms

Lower length bounds pass to left matrix multiplication (the upper bound
`specNorm_le_of_mulVec_sq_le` is in `NLAlib.Matrix.Norms.SpectralNormBounds`). These finite-dimensional facts
support the Sylvester separation and subspace perturbation results.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] [DecidableEq n] in
/-- A lower Euclidean length bound for a matrix passes to left multiplication
in the spectral norm. Source: centered Sylvester proof, toolkit derivations §5.3. -/
theorem mul_specNorm_le_specNorm_mul_of_mulVec_sq_le {T : Matrix m n ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ x : n → ℝ, c ^ 2 * (x ⬝ᵥ x) ≤ (T *ᵥ x) ⬝ᵥ (T *ᵥ x))
    (X : Matrix n p ℝ) : c * specNorm X ≤ specNorm (T * X) := by
  by_cases hc0 : c = 0
  · simp [hc0, specNorm_nonneg]
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hb : specNorm X ≤ specNorm (T * X) / c := by
    apply specNorm_le_of_mulVec_sq_le (div_nonneg (specNorm_nonneg _) hc)
    intro x
    have hh := h (X *ᵥ x)
    have hu := sum_sq_mulVec_le_specNorm_sq (T * X) x
    simp only [← Matrix.mulVec_mulVec] at hu
    have hu' : (T *ᵥ (X *ᵥ x)) ⬝ᵥ (T *ᵥ (X *ᵥ x)) ≤
        specNorm (T * X) ^ 2 * (x ⬝ᵥ x) := by
      simpa [dotProduct, sq, Matrix.mulVec_mulVec] using hu
    have hh' := hh.trans hu'
    rw [div_pow, div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hcpos)).2
    nlinarith [hh']
  have := (le_div_iff₀ hcpos).1 hb
  nlinarith

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- The same pointwise expansion passes to the squared Frobenius norm by
summing columns. Source: centered Sylvester proof, toolkit derivations §5.3. -/
theorem mul_frobSq_le_frobSq_mul_of_mulVec_sq_le {T : Matrix m n ℝ} {c : ℝ}
    (h : ∀ x : n → ℝ, c ^ 2 * (x ⬝ᵥ x) ≤ (T *ᵥ x) ⬝ᵥ (T *ᵥ x))
    (X : Matrix n p ℝ) : c ^ 2 * frobSq X ≤ frobSq (T * X) := by
  rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq,
    Finset.sum_comm (f := fun i j => X i j ^ 2),
    Finset.sum_comm (f := fun i j => (T * X) i j ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    simpa [dotProduct, sq, Matrix.mul_apply, Matrix.mulVec] using h (fun i => X i j)

end NLAlib
