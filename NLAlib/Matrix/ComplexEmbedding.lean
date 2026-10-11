import NLAlib.Matrix.ComplexFrobenius
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Complex Gram error and squared norm preservation

The Euclidean quadratic form of a Gram error gives the source's complex
subspace embedding inequalities. Source: operator re-derivation `sa:leverage`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- The squared Euclidean norm is the real self dot product.
Source: the Euclidean inner product definition; supports `leverage-sampling-ose`. -/
theorem norm_toLp_sq_eq_re_star_dotProduct {n : Type*} [Fintype n] (x : n → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 = (star x ⬝ᵥ x).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, RCLike.re_eq_complex_re]

/-- A complex matrix's quadratic form is bounded by its operator norm times
the vector's squared Euclidean norm. Source: Cauchy–Schwarz and the operator
norm definition; supports `leverage-sampling-ose`. -/
theorem abs_re_star_dotProduct_mulVec_le_norm
    {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (x : n → ℂ) :
    |(star x ⬝ᵥ (H *ᵥ x)).re| ≤ ‖H‖ *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
  have hin : inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ n)
      (WithLp.toLp 2 (H *ᵥ x) : EuclideanSpace ℂ n) = star x ⬝ᵥ (H *ᵥ x) := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have hh := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ n)
    (WithLp.toLp 2 (H *ᵥ x) : EuclideanSpace ℂ n)
  rw [hin] at hh
  calc _ ≤ ‖star x ⬝ᵥ (H *ᵥ x)‖ := Complex.abs_re_le_norm _
    _ ≤ _ := hh
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ *
        (‖H‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖) := by
      gcongr
      exact H.l2_opNorm_mulVec (WithLp.toLp 2 x)
    _ = _ := by ring

/-- A complex Gram error bounded by `ε` preserves every squared Euclidean norm
between `1−ε` and `1+ε`. Source: operator re-derivation `sa:leverage-theorem`. -/
theorem norm_mulVec_sq_bounds_of_norm_gram_sub_one_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (T : Matrix m n ℂ) {ε : ℝ} (h : ‖Tᴴ * T - 1‖ ≤ ε) (x : n → ℂ) :
    (1 - ε) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 ≤
        ‖(WithLp.toLp 2 (T *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ∧
      ‖(WithLp.toLp 2 (T *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ≤
        (1 + ε) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
  have hq : (star x ⬝ᵥ ((Tᴴ * T - 1) *ᵥ x)).re =
      ‖(WithLp.toLp 2 (T *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 -
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, Complex.sub_re,
      norm_toLp_sq_eq_re_star_dotProduct, norm_toLp_sq_eq_re_star_dotProduct,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  have hh := (abs_re_star_dotProduct_mulVec_le_norm (Tᴴ * T - 1) x).trans
    (mul_le_mul_of_nonneg_right h (sq_nonneg _))
  rw [hq, abs_le] at hh
  constructor <;> nlinarith

end NLAlib
