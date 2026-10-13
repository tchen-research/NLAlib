import NLAlib.Matrix.Spectral.Core
import NLAlib.Matrix.Spectral.SpectralBounds
/-!
# Extreme singular bounds from a scaled Gram error

The deterministic last step of the independent isotropic row theorem (Vershynin 2012, proof of
Thm 5.39): a Gram error `‖AᵀA − N I‖₂ ≤ N max(α, α²)` traps both extreme singular values of `A`
in `[√N(1 − α), √N(1 + α)]`. Supports `subgaussian-matrix-norm`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A Gram error `‖AᵀA − N I‖₂ ≤ N max(α, α²)` gives `√N(1 − α) ≤ σ_min(A)`, with
`σ_min(A) = singularValues A (card n - 1)`; trivial when `α ≥ 1`. Vershynin 2012, Lemma 5.36
(lower half); supports `subgaussian-matrix-norm`. -/
theorem sqrt_mul_one_sub_le_singularValues_last_of_gram_error [Nonempty n]
    (A : Matrix m n ℝ) {N α : ℝ} (hN : 0 ≤ N) (hα : 0 ≤ α)
    (h : specNorm (Aᵀ * A - N • 1) ≤ N * max α (α ^ 2)) :
    Real.sqrt N * (1 - α) ≤ singularValues A (Fintype.card n - 1) := by
  rcases le_or_gt α 1 with hα1 | hα1
  · apply le_singularValues_last A
    intro x hx
    have hx' : x ⬝ᵥ x = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hx, one_pow]
    have hh := abs_dotProduct_mulVec_le_specNorm (Aᵀ * A - N • 1) x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hx', mul_one, mul_one,
      ← show (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) from
        star_mulVec_dotProduct_mulVec_self A x] at hh
    have hh' := (abs_le.mp (hh.trans h)).1
    have hmax : max α (α ^ 2) = α := max_eq_left (by nlinarith)
    rw [hmax] at hh'
    have hs := Real.sq_sqrt hN
    have hss := norm_toLp_sq_eq_dotProduct_self (A *ᵥ x)
    have hnon : 0 ≤ Real.sqrt N * (1 - α) := by positivity
    have hlow : (Real.sqrt N * (1 - α)) ^ 2 ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
      rw [mul_pow, hs, hss]
      nlinarith [mul_nonneg hN (mul_nonneg hα (sub_nonneg.mpr hα1))]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hlow
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg N)
      (by linarith)).trans (singularValues_nonneg A _)

open scoped Matrix.Norms.L2Operator in
/-- A Gram error `‖AᵀA − N I‖₂ ≤ N max(α, α²)` gives `‖A‖₂ ≤ √N(1 + α)`, including `N = 0`.
Vershynin 2012, Lemma 5.36 (upper half); supports `subgaussian-matrix-norm`. -/
theorem specNorm_le_sqrt_mul_one_add_of_gram_error (A : Matrix m n ℝ) {N α : ℝ} (hN : 0 ≤ N)
    (hα : 0 ≤ α) (h : specNorm (Aᵀ * A - N • 1) ≤ N * max α (α ^ 2)) :
    specNorm A ≤ Real.sqrt N * (1 + α) := by
  have hupper : 1 + max α (α ^ 2) ≤ (1 + α) ^ 2 := by
    have hm : max α (α ^ 2) ≤ (1 + α) ^ 2 - 1 :=
      max_le (by nlinarith) (by nlinarith)
    linarith
  have hh : specNorm A ^ 2 ≤ N * max α (α ^ 2) + N := by
    have hsq : specNorm A ^ 2 = specNorm (Aᵀ * A) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        specNorm_sq_eq_specNorm_conjTranspose_mul_self A
    rw [hsq]
    have hdecomp : Aᵀ * A = (Aᵀ * A - N • 1) + N • 1 := (sub_add_cancel _ _).symm
    calc _ = specNorm ((Aᵀ * A - N • 1) + N • 1) := congrArg specNorm hdecomp
      _ ≤ specNorm (Aᵀ * A - N • 1) + specNorm (N • (1 : Matrix n n ℝ)) :=
        specNorm_add_le _ _
      _ ≤ N * max α (α ^ 2) + N := by
        gcongr
        rw [specNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hN, ← specNorm_eq_norm]
        exact (mul_le_mul_of_nonneg_left (specNorm_one_le (n := n)) hN).trans_eq (mul_one _)
  have hs := Real.sq_sqrt hN
  have hnon : 0 ≤ Real.sqrt N * (1 + α) := by positivity
  have hhigh : specNorm A ^ 2 ≤ (Real.sqrt N * (1 + α)) ^ 2 := by
    rw [mul_pow, hs]
    nlinarith [mul_le_mul_of_nonneg_left hupper hN]
  exact le_of_pow_le_pow_left₀ two_ne_zero hnon hhigh

end NLAlib
