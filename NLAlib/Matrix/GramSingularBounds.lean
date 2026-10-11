import NLAlib.Matrix.Spectral

/-!
# Extreme singular bounds from a scaled Gram error

The deterministic last step of the independent isotropic row theorem.
Source: operator re-derivation `pg:row-bound`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- A Gram error bounded by `N max(α,α²)` controls both domain-based extreme
singular values by `√N(1 ± α)`, including when `α ≥ 1` or `N = 0`.
Source: operator re-derivation `pg:row-bound`; supports
`subgaussian-matrix-norm`. -/
theorem sigmaMin_specNorm_bounds_of_gram_error
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty n]
    (A : Matrix m n ℝ) {N α : ℝ} (hN : 0 ≤ N) (hα : 0 ≤ α)
    (h : specNorm (Aᵀ * A - N • 1) ≤ N * max α (α ^ 2)) :
    Real.sqrt N * (1 - α) ≤ sigmaMin A ∧
      specNorm A ≤ Real.sqrt N * (1 + α) := by
  have hupper : 1 + max α (α ^ 2) ≤ (1 + α) ^ 2 := by
    have hm : max α (α ^ 2) ≤ (1 + α) ^ 2 - 1 :=
      max_le (by nlinarith) (by nlinarith)
    linarith
  have hunit : ∀ x : n → ℝ, x ⬝ᵥ x = 1 →
      |(A *ᵥ x) ⬝ᵥ (A *ᵥ x) - N| ≤ N * max α (α ^ 2) := by
    intro x hx
    have hh := abs_dotProduct_mulVec_le_specNorm (Aᵀ * A - N • 1) x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hx, mul_one, mul_one,
      ← mulVec_dotProduct_mulVec_self] at hh
    exact hh.trans h
  constructor
  · rcases le_or_gt α 1 with hα1 | hα1
    · apply le_sigmaMin A
      intro x hx
      have hh := (abs_le.mp (hunit x hx)).1
      have hmax : max α (α ^ 2) = α := max_eq_left (by nlinarith)
      rw [hmax] at hh
      have hs := Real.sq_sqrt hN
      have hss := Real.sq_sqrt (dotProduct_self_nonneg (A *ᵥ x))
      have hnon : 0 ≤ Real.sqrt N * (1 - α) := by positivity
      have hlow : (Real.sqrt N * (1 - α)) ^ 2 ≤
          (Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))) ^ 2 := by
        rw [mul_pow, hs, hss]
        nlinarith [mul_nonneg hN (mul_nonneg hα (sub_nonneg.mpr hα1))]
      nlinarith [Real.sqrt_nonneg ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))]
    · exact (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg N)
        (by linarith)).trans (sigmaMin_nonneg A)
  · have hh : specNorm A ^ 2 ≤ N * max α (α ^ 2) + N := by
      have hsq : specNorm A ^ 2 = specNorm (Aᵀ * A) := by
        simpa only [Matrix.transpose_transpose, specNorm_transpose] using
          (specNorm_mul_transpose_self Aᵀ).symm
      rw [hsq]
      have hdecomp : Aᵀ * A = (Aᵀ * A - N • 1) + N • 1 := (sub_add_cancel _ _).symm
      calc _ = specNorm ((Aᵀ * A - N • 1) + N • 1) := congrArg specNorm hdecomp
        _ ≤ specNorm (Aᵀ * A - N • 1) + specNorm (N • (1 : Matrix n n ℝ)) :=
          specNorm_add_le _ _
        _ ≤ N * max α (α ^ 2) + N := by
          gcongr
          rw [specNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hN]
          exact (mul_le_mul_of_nonneg_left (specNorm_one_le (n := n)) hN).trans_eq (mul_one _)
    have hs := Real.sq_sqrt hN
    have hnon : 0 ≤ Real.sqrt N * (1 + α) := by positivity
    have hhigh : specNorm A ^ 2 ≤
        (Real.sqrt N * (1 + α)) ^ 2 := by
      rw [mul_pow, hs]
      nlinarith [mul_le_mul_of_nonneg_left hupper hN]
    nlinarith [specNorm_nonneg A]

end NLAlib
