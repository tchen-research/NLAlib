import NLAlib.Matrix.MoorePenrose
import NLAlib.LowRank.SketchedRegression
import NLAlib.Matrix.Gram

/-!
# The raw generalized Nyström formula and its orthonormal-frame form

The raw sketch uses the general Moore–Penrose inverse even when the first
sketch is rank deficient. Full column/row rank permits the reverse-order
identity that identifies it with the existing orthonormal-frame estimator.

Source: Tropp–Webber 2023, Section 5. Atlas: `gn-expected-error`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib

/-- Reverse order for a full-column-rank left factor and full-row-rank right
factor. This includes empty intermediate spaces. The proof checks the four
Penrose identities and uses uniqueness. Atlas: `pseudoinverse`, `gn-expected-error`. -/
theorem moorePenroseInverse_mul_eq_pinvR_mul_pinvL
    {m q p : Type*} [Fintype m] [Fintype q] [Fintype p] [DecidableEq q]
    (M : Matrix m q ℝ) (R : Matrix q p ℝ)
    (hM : IsUnit (Mᵀ * M)) (hR : IsUnit (R * Rᵀ)) :
    moorePenroseInverse (M * R) = pinvR R * pinvL M := by
  classical
  have hML := pinvL_mul hM
  have hRP := mul_pinvR hR
  apply (isMoorePenroseInverse (M * R)).unique
  constructor
  · calc
      (M * R) * (pinvR R * pinvL M) * (M * R) =
          M * (R * pinvR R) * (pinvL M * M) * R := by simp only [Matrix.mul_assoc]
      _ = M * R := by rw [hRP, hML]; simp
  · calc
      (pinvR R * pinvL M) * (M * R) * (pinvR R * pinvL M) =
          pinvR R * (pinvL M * M) * (R * pinvR R) * pinvL M := by
            simp only [Matrix.mul_assoc]
      _ = pinvR R * pinvL M := by rw [hML, hRP]; simp
  · have hEq : (M * R) * (pinvR R * pinvL M) = M * pinvL M := by
      calc
        _ = M * (R * pinvR R) * pinvL M := by simp only [Matrix.mul_assoc]
        _ = M * pinvL M := by rw [hRP]; simp
    rw [hEq]
    exact mul_pinvL_isSymm M
  · have hEq : (pinvR R * pinvL M) * (M * R) = pinvR R * R := by
      calc
        _ = pinvR R * (pinvL M * M) * R := by simp only [Matrix.mul_assoc]
        _ = pinvR R * R := by rw [hML]; simp
    rw [hEq]
    exact pinvR_mul_isSymm R

/-- If a frame factorization has exactly as many columns as the sketch rank,
the coordinate matrix has invertible row Gram matrix.
Source: rank invariance under a left inverse; atlas `gn-expected-error`. -/
theorem isUnit_rowGram_of_frame_factorization
    {m q t : Type*} [Fintype m] [Fintype q] [Fintype t] [DecidableEq q]
    (Q : Matrix m q ℝ) (Y : Matrix m t ℝ)
    (hY : Q * (Qᵀ * Y) = Y) (hRank : Y.rank = Fintype.card q) :
    IsUnit ((Qᵀ * Y) * (Qᵀ * Y)ᵀ) := by
  classical
  have hRankR : (Qᵀ * Y).rank = Y.rank := by
    apply le_antisymm (Matrix.rank_mul_le_right Qᵀ Y)
    calc
      Y.rank = (Q * (Qᵀ * Y)).rank := congrArg Matrix.rank hY.symm
      _ ≤ (Qᵀ * Y).rank := Matrix.rank_mul_le_right Q (Qᵀ * Y)
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.2
  apply det_ne_zero_of_rank_eq
  rw [Matrix.rank_self_mul_transpose, hRankR, hRank]

/-- The actual raw generalized Nyström estimator, using a general
Moore–Penrose inverse. Rank-deficient sketches are included.
Source: Tropp–Webber 2023, Section 5. Atlas: `gn-expected-error`. -/
def rawGeneralizedNystrom {m n t s : Type*}
    [Fintype m] [Fintype n] [Fintype t] [Fintype s]
    (A : Matrix m n ℝ) (Y : Matrix m t ℝ) (Ψ : Matrix m s ℝ) : Matrix m n ℝ :=
  Y * moorePenroseInverse (Ψᵀ * Y) * (Ψᵀ * A)

/-- The raw generalized Nyström output agrees with the normalized-frame
output whenever the supplied frame has the exact sketch rank and the second
sketch is injective on that frame. No full rank of the raw first sketch is
assumed. Source: Tropp–Webber 2023, Section 5; atlas `gn-expected-error`. -/
theorem rawGeneralizedNystrom_eq_sketchedOutput
    {m n q t s : Type*} [Fintype m] [Fintype n] [Fintype q] [Fintype t] [Fintype s]
    [DecidableEq q] (A : Matrix m n ℝ) (Y : Matrix m t ℝ)
    (Q : Matrix m q ℝ) (Ψ : Matrix m s ℝ)
    (hY : Q * (Qᵀ * Y) = Y) (hRank : Y.rank = Fintype.card q)
    (hΨ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    rawGeneralizedNystrom A Y Ψ = sketchedOutput Q Ψ A := by
  let R := Qᵀ * Y
  have hR : IsUnit (R * Rᵀ) := isUnit_rowGram_of_frame_factorization Q Y hY hRank
  have hFactor : Ψᵀ * Y = (Ψᵀ * Q) * R := by
    rw [← hY]
    simp only [R, Matrix.mul_assoc]
  rw [rawGeneralizedNystrom, hFactor,
    moorePenroseInverse_mul_eq_pinvR_mul_pinvL (Ψᵀ * Q) R hΨ hR]
  calc
    Y * (pinvR R * pinvL (Ψᵀ * Q)) * (Ψᵀ * A) =
        Q * (R * pinvR R) * pinvL (Ψᵀ * Q) * (Ψᵀ * A) := by
          rw [← hY]
          simp only [R, Matrix.mul_assoc]
    _ = sketchedOutput Q Ψ A := by
      rw [mul_pinvR hR]
      simp only [Matrix.mul_one, sketchedOutput, sketchedCore, Matrix.mul_assoc]

end NLAlib
