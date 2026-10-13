import NLAlib.Matrix.Norms.Frobenius

/-!
# Normal block triangular matrices are block diagonal

The leading Gram-block trace identity forces the off-diagonal block to have
zero Frobenius mass. Source: Horn–Johnson (2013), Lemma 2.5.2;
atlas `normal-matrices`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A complex upper block triangular normal matrix has zero off-diagonal
block. Source: Horn–Johnson (2013), Lemma 2.5.2; the proof is a leading-block
trace identity and includes empty row or column blocks.
atlas: normal-matrices (partial) -/
theorem eq_zero_of_normal_upper_fromBlocks {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    {C : Matrix m n ℂ}
    (hM : Matrix.fromBlocks A C 0 B * (Matrix.fromBlocks A C 0 B)ᴴ =
      (Matrix.fromBlocks A C 0 B)ᴴ * Matrix.fromBlocks A C 0 B) : C = 0 := by
  have h := congrArg (fun M : Matrix (m ⊕ n) (m ⊕ n) ℂ => M.toBlocks₁₁.trace) hM
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, Matrix.trace_add] at h
  have htr : (C * Cᴴ).trace = 0 := by
    rw [Matrix.trace_mul_comm A Aᴴ] at h
    exact add_left_cancel (by simpa only [add_zero] using h)
  have hsq : frobSq C = 0 := by
    rw [frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.trace_mul_comm, htr]
    rfl
  exact (frobSq_eq_zero_iff C).mp hsq

/-- An upper block triangular normal matrix equals its block diagonal part.
Source: Horn–Johnson (2013), Lemma 2.5.2.
atlas: normal-matrices (partial) -/
theorem upper_fromBlocks_eq_diagonal_of_normal {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    {C : Matrix m n ℂ}
    (hM : Matrix.fromBlocks A C 0 B * (Matrix.fromBlocks A C 0 B)ᴴ =
      (Matrix.fromBlocks A C 0 B)ᴴ * Matrix.fromBlocks A C 0 B) :
    Matrix.fromBlocks A C 0 B = Matrix.fromBlocks A 0 0 B := by
  rw [eq_zero_of_normal_upper_fromBlocks hM]

end NLAlib
