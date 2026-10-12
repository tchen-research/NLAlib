import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic
/-!
# The Penrose identities

`IsMoorePenroseInverse A B`: the four Penrose identities `ABA = A`, `BAB = B`, `(AB)ᵀ = AB`,
`(BA)ᵀ = BA` for real rectangular matrices over arbitrary finite index types (empty types and
rank-deficient matrices included), and their purely algebraic consequences: uniqueness
(`IsMoorePenroseInverse.unique`), symmetry under swapping, transposition, reindexing and
orthogonal changes of coordinates, idempotence and range of the projectors `AB`, `BA`, and the
Gram identity `(AᵀA)⁺ = A⁺A⁺ᵀ` (`IsMoorePenroseInverse.transpose_mul_self`).
Existence and the canonical inverse `moorePenroseInverse` (through the SVD) are in
`Matrix/Basic/MoorePenrose.lean`.

Source: Horn–Johnson, Matrix Analysis, §7.3. Atlas: `pseudoinverse`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- The four Penrose identities for a real matrix and a candidate pseudoinverse.
No rank assumption is imposed. Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
structure IsMoorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop where
  /-- The first Penrose identity, `A B A = A`. -/
  mul_mul_eq : A * B * A = A
  /-- The second Penrose identity, `B A B = B`. -/
  inv_mul_inv_eq : B * A * B = B
  /-- The image-space projector is symmetric. -/
  transpose_mul_eq : (A * B)ᵀ = A * B
  /-- The row-space projector is symmetric. -/
  transpose_inv_mul_eq : (B * A)ᵀ = B * A

namespace IsMoorePenroseInverse

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  {A : Matrix m n ℝ} {B C : Matrix n m ℝ}

/-- The Moore–Penrose inverse is unique, also for zero-rank and empty matrices.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem unique (hB : IsMoorePenroseInverse A B) (hC : IsMoorePenroseInverse A C) :
    B = C := by
  have hBA : (B * A) * (C * A) = B * A := by
    calc
      (B * A) * (C * A) = B * (A * C * A) := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [hC.mul_mul_eq]
  have hCA : (C * A) * (B * A) = C * A := by
    calc
      (C * A) * (B * A) = C * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = C * A := by rw [hB.mul_mul_eq]
  have hBAeq : B * A = C * A := by
    have ht := congrArg Matrix.transpose hBA
    simp only [Matrix.transpose_mul, hC.transpose_inv_mul_eq,
      hB.transpose_inv_mul_eq] at ht
    rw [hCA] at ht
    exact ht.symm
  have hAB : (A * B) * (A * C) = A * C := by
    calc
      (A * B) * (A * C) = (A * B * A) * C := by simp only [Matrix.mul_assoc]
      _ = A * C := by rw [hB.mul_mul_eq]
  have hAC : (A * C) * (A * B) = A * B := by
    calc
      (A * C) * (A * B) = (A * C * A) * B := by simp only [Matrix.mul_assoc]
      _ = A * B := by rw [hC.mul_mul_eq]
  have hABeq : A * B = A * C := by
    have ht := congrArg Matrix.transpose hAB
    simp only [Matrix.transpose_mul, hC.transpose_mul_eq, hB.transpose_mul_eq] at ht
    rw [hAC] at ht
    exact ht
  calc
    B = B * A * B := hB.inv_mul_inv_eq.symm
    _ = C * A * B := by rw [hBAeq]
    _ = C * (A * B) := Matrix.mul_assoc _ _ _
    _ = C * (A * C) := by rw [hABeq]
    _ = C * A * C := (Matrix.mul_assoc _ _ _).symm
    _ = C := hC.inv_mul_inv_eq

/-- Exchanging a matrix and its Moore–Penrose inverse preserves the four
identities. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem swap (h : IsMoorePenroseInverse A B) : IsMoorePenroseInverse B A :=
  ⟨h.inv_mul_inv_eq, h.mul_mul_eq, h.transpose_inv_mul_eq, h.transpose_mul_eq⟩

/-- Transposing both matrices preserves the Penrose identities.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem transpose (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse Aᵀ Bᵀ := by
  constructor
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose h.mul_mul_eq
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose h.inv_mul_inv_eq
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      h.transpose_inv_mul_eq.symm
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      h.transpose_mul_eq.symm

/-- Equivalent row and column indexing preserves the Penrose identities.
This transports the SVD construction to arbitrary finite index types. -/
theorem submatrix (h : IsMoorePenroseInverse A B) (em : p ≃ m) (en : q ≃ n) :
    IsMoorePenroseInverse (A.submatrix em en) (B.submatrix en em) := by
  constructor
  · simpa only [Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix m n ℝ => M.submatrix em en) h.mul_mul_eq
  · simpa only [Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix n m ℝ => M.submatrix en em) h.inv_mul_inv_eq
  · simpa only [Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix] using
      congrArg (fun M : Matrix m m ℝ => M.submatrix em em) h.transpose_mul_eq
  · simpa only [Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix] using
      congrArg (fun M : Matrix n n ℝ => M.submatrix en en) h.transpose_inv_mul_eq

/-- Orthogonal changes of row and column coordinates transport a Moore–Penrose
inverse by the reversed changes. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem orthogonal_transform [DecidableEq m] [DecidableEq n]
    (h : IsMoorePenroseInverse A B) (U : Matrix m m ℝ) (V : Matrix n n ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsMoorePenroseInverse (U * A * Vᵀ) (V * B * Uᵀ) := by
  constructor
  · calc
      (U * A * Vᵀ) * (V * B * Uᵀ) * (U * A * Vᵀ) =
          U * (A * (Vᵀ * V) * B * (Uᵀ * U) * A) * Vᵀ := by
            simp only [Matrix.mul_assoc]
      _ = U * A * Vᵀ := by
        rw [hU, hV, Matrix.mul_one, Matrix.mul_one, h.mul_mul_eq]
  · calc
      (V * B * Uᵀ) * (U * A * Vᵀ) * (V * B * Uᵀ) =
          V * (B * (Uᵀ * U) * A * (Vᵀ * V) * B) * Uᵀ := by
            simp only [Matrix.mul_assoc]
      _ = V * B * Uᵀ := by
        rw [hU, hV, Matrix.mul_one, Matrix.mul_one, h.inv_mul_inv_eq]
  · have he : (U * A * Vᵀ) * (V * B * Uᵀ) = U * (A * B) * Uᵀ := by
      calc
        _ = U * (A * (Vᵀ * V) * B) * Uᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
    rw [he]
    calc
      (U * (A * B) * Uᵀ)ᵀ = U * (A * B)ᵀ * Uᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = U * (A * B) * Uᵀ := by rw [h.transpose_mul_eq]
  · have he : (V * B * Uᵀ) * (U * A * Vᵀ) = V * (B * A) * Vᵀ := by
      calc
        _ = V * (B * (Uᵀ * U) * A) * Vᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]
    rw [he]
    calc
      (V * (B * A) * Vᵀ)ᵀ = V * (B * A)ᵀ * Vᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = V * (B * A) * Vᵀ := by rw [h.transpose_inv_mul_eq]

/-- `A B` is an idempotent image-space projector. Together with the third
Penrose identity this is an orthogonal projector. -/
theorem mul_isIdempotentElem (h : IsMoorePenroseInverse A B) :
    IsIdempotentElem (A * B) := by
  change (A * B) * (A * B) = A * B
  calc
    _ = (A * B * A) * B := by simp only [Matrix.mul_assoc]
    _ = A * B := by rw [h.mul_mul_eq]

/-- `B A` is an idempotent row-space projector. -/
theorem inv_mul_isIdempotentElem (h : IsMoorePenroseInverse A B) :
    IsIdempotentElem (B * A) := h.swap.mul_isIdempotentElem

/-- The fixed vectors of the image-space projector are exactly the image of
the original matrix, including rank-deficient and empty matrices. -/
theorem mulVec_eq_self_iff (h : IsMoorePenroseInverse A B) (x : m → ℝ) :
    (A * B) *ᵥ x = x ↔ ∃ y : n → ℝ, A *ᵥ y = x := by
  constructor
  · intro hx
    exact ⟨B *ᵥ x, by rw [Matrix.mulVec_mulVec]; exact hx⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_mulVec, h.mul_mul_eq]

/-- The image of `A B` equals the image of `A`: the symmetric idempotent
`A B` is the orthogonal projector onto the original column space. -/
theorem range_mul_eq (h : IsMoorePenroseInverse A B) :
    LinearMap.range (A * B).mulVecLin = LinearMap.range A.mulVecLin := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨B *ᵥ y, by simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨A *ᵥ y, by simp only [Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, h.mul_mul_eq]⟩

/-- The Moore–Penrose inverse of a column Gram matrix is the corresponding
Gram matrix of the inverse. This identity holds at every rank.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem transpose_mul_self (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse (Aᵀ * A) (B * Bᵀ) := by
  have hCG : (B * Bᵀ) * (Aᵀ * A) = B * A := by
    calc
      _ = B * (A * B)ᵀ * A := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B * (A * B) * A := by rw [h.transpose_mul_eq]
      _ = (B * A * B) * A := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [h.inv_mul_inv_eq]
  have hGC : (Aᵀ * A) * (B * Bᵀ) = B * A := by
    calc
      _ = ((B * Bᵀ) * (Aᵀ * A))ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = (B * A)ᵀ := by rw [hCG]
      _ = B * A := h.transpose_inv_mul_eq
  constructor
  · calc
      _ = (Aᵀ * A) * ((B * Bᵀ) * (Aᵀ * A)) := Matrix.mul_assoc _ _ _
      _ = (Aᵀ * A) * (B * A) := by rw [hCG]
      _ = Aᵀ * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = Aᵀ * A := by rw [h.mul_mul_eq]
  · calc
      _ = (B * A) * (B * Bᵀ) := by rw [hCG]
      _ = (B * A * B) * Bᵀ := by simp only [Matrix.mul_assoc]
      _ = B * Bᵀ := by rw [h.inv_mul_inv_eq]
  · rw [hGC]
    exact h.transpose_inv_mul_eq
  · rw [hCG]
    exact h.transpose_inv_mul_eq

end IsMoorePenroseInverse

end NLAlib
