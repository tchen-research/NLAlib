import NLAlib.Matrix.Subspaces.ProjectorBlocks
import Mathlib.Algebra.Star.StarProjection

/-!
# Projection costs depend only on the Gram matrix

The squared Frobenius residual of an orthogonal projector is a linear trace
functional of the row Gram matrix. These identities supply fixed-offset
projection-cost certificates without choosing singular vectors.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n l : Type*}
  [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- The squared residual of an orthogonal projector is the real trace of the
complement against the row Gram matrix. Cohen–Elder–Musco–Musco–Persu 2015, §3. -/
theorem frobSq_one_sub_mul_eq_re_trace {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    frobSq ((1 - P) * A) = RCLike.re ((1 - P) * (A * Aᴴ)).trace := by
  have hs : (1 - P)ᴴ = 1 - P := hP.one_sub.isSelfAdjoint.star_eq
  have hi : (1 - P) * (1 - P) = 1 - P := hP.one_sub.isIdempotentElem
  rw [frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.conjTranspose_mul, hs,
    Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc (1 - P), hi,
    Matrix.trace_mul_comm Aᴴ, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Two sketch factors with the same row Gram matrix have identical costs
for every left residual map, without any rank or projector hypothesis. -/
theorem frobSq_mul_eq_of_mul_conjTranspose_eq {A : Matrix m n 𝕜}
    {B : Matrix m l 𝕜} (h : A * Aᴴ = B * Bᴴ) (C : Matrix m m 𝕜) :
    frobSq (C * A) = frobSq (C * B) := by
  rw [frobSq_eq_re_trace_mul_conjTranspose, frobSq_eq_re_trace_mul_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A, h]

/-- With a fixed offset, the discrepancy between sketch and original costs
is `c - Re tr D + Re tr (P D)`, where `D = A Aᴴ - B Bᴴ`.
Cohen–Elder–Musco–Musco–Persu 2015, §3. -/
theorem frobSq_one_sub_mul_add_sub_eq {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (B : Matrix m l 𝕜) (c : ℝ) :
    frobSq ((1 - P) * B) + c - frobSq ((1 - P) * A) =
      c - RCLike.re (A * Aᴴ - B * Bᴴ).trace +
        RCLike.re (P * (A * Aᴴ - B * Bᴴ)).trace := by
  rw [frobSq_one_sub_mul_eq_re_trace hP, frobSq_one_sub_mul_eq_re_trace hP]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.trace_sub, map_sub]
  ring

end NLAlib
