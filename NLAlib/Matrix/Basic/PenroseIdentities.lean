import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# The Penrose identities

`IsMoorePenroseInverse A B`: the four Penrose identities `ABA = A`, `BAB = B`, `(AB)ᴴ = AB`,
`(BA)ᴴ = BA` for rectangular matrices over `𝕜` (`ℝ` or `ℂ`, through `[RCLike 𝕜]`) with arbitrary
finite index types (empty types and rank-deficient matrices included), and their purely
algebraic consequences: uniqueness (`IsMoorePenroseInverse.unique`), symmetry under swapping,
(conjugate) transposition, reindexing and unitary changes of coordinates, idempotence and range of
the projectors `AB`, `BA`, and the Gram identity `(AᴴA)⁺ = A⁺A⁺ᴴ`
(`IsMoorePenroseInverse.conjTranspose_mul_self`).

Over `ℝ` the conjugate transpose is definitionally the transpose, so the structure is the old
real one: `⟨h₁, h₂, h₃, h₄⟩` accepts `ᵀ` proofs of the last two fields, and
`Matrix.conjTranspose_eq_transpose_of_trivial` (`@[simp]`) turns the `ᴴ` fields into `ᵀ` goals.
Existence and the canonical inverse `moorePenroseInverse` (through the SVD) are in
`Matrix/Basic/MoorePenrose.lean`.

Source: Horn–Johnson, Matrix Analysis, §7.3. Atlas: `pseudoinverse`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- The four Penrose identities for a matrix and a candidate pseudoinverse, over `ℝ` or `ℂ`:
`A B A = A`, `B A B = B`, and `A B`, `B A` are Hermitian. No rank assumption is imposed.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
structure IsMoorePenroseInverse {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) : Prop where
  /-- The first Penrose identity, `A B A = A`. -/
  mul_mul_eq : A * B * A = A
  /-- The second Penrose identity, `B A B = B`. -/
  inv_mul_inv_eq : B * A * B = B
  /-- The image-space projector is Hermitian. -/
  conjTranspose_mul_eq : (A * B)ᴴ = A * B
  /-- The row-space projector is Hermitian. -/
  conjTranspose_inv_mul_eq : (B * A)ᴴ = B * A

namespace IsMoorePenroseInverse

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Fintype q] {A : Matrix m n 𝕜} {B C : Matrix n m 𝕜}

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
    have ht := congrArg Matrix.conjTranspose hBA
    simp only [Matrix.conjTranspose_mul, hC.conjTranspose_inv_mul_eq,
      hB.conjTranspose_inv_mul_eq] at ht
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
    have ht := congrArg Matrix.conjTranspose hAB
    simp only [Matrix.conjTranspose_mul, hC.conjTranspose_mul_eq,
      hB.conjTranspose_mul_eq] at ht
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
  ⟨h.inv_mul_inv_eq, h.mul_mul_eq, h.conjTranspose_inv_mul_eq, h.conjTranspose_mul_eq⟩

/-- Conjugate-transposing both matrices preserves the Penrose identities.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem conjTranspose (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse Aᴴ Bᴴ := by
  constructor
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose h.mul_mul_eq
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose h.inv_mul_inv_eq
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      h.conjTranspose_inv_mul_eq.symm
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      h.conjTranspose_mul_eq.symm

/-- Transposing both matrices preserves the Penrose identities (over `ℂ` too: the transpose
of a Hermitian matrix is Hermitian). Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem transpose (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse Aᵀ Bᵀ := by
  constructor
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose h.mul_mul_eq
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose h.inv_mul_inv_eq
  · rw [← Matrix.transpose_mul, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      h.conjTranspose_inv_mul_eq]
  · rw [← Matrix.transpose_mul, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      h.conjTranspose_mul_eq]

/-- Equivalent row and column indexing preserves the Penrose identities.
This transports the SVD construction to arbitrary finite index types. -/
theorem submatrix (h : IsMoorePenroseInverse A B) (em : p ≃ m) (en : q ≃ n) :
    IsMoorePenroseInverse (A.submatrix em en) (B.submatrix en em) := by
  constructor
  · simpa only [Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix m n 𝕜 => M.submatrix em en) h.mul_mul_eq
  · simpa only [Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix n m 𝕜 => M.submatrix en em) h.inv_mul_inv_eq
  · simpa only [Matrix.submatrix_mul_equiv, Matrix.conjTranspose_submatrix] using
      congrArg (fun M : Matrix m m 𝕜 => M.submatrix em em) h.conjTranspose_mul_eq
  · simpa only [Matrix.submatrix_mul_equiv, Matrix.conjTranspose_submatrix] using
      congrArg (fun M : Matrix n n 𝕜 => M.submatrix en en) h.conjTranspose_inv_mul_eq

/-- Unitary changes of row and column coordinates (`Uᴴ U = 1`, `Vᴴ V = 1`) transport a
Moore–Penrose inverse by the reversed changes. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem unitary_transform [DecidableEq m] [DecidableEq n]
    (h : IsMoorePenroseInverse A B) (U : Matrix m m 𝕜) (V : Matrix n n 𝕜)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    IsMoorePenroseInverse (U * A * Vᴴ) (V * B * Uᴴ) := by
  constructor
  · calc
      (U * A * Vᴴ) * (V * B * Uᴴ) * (U * A * Vᴴ) =
          U * (A * (Vᴴ * V) * B * (Uᴴ * U) * A) * Vᴴ := by
            simp only [Matrix.mul_assoc]
      _ = U * A * Vᴴ := by
        rw [hU, hV, Matrix.mul_one, Matrix.mul_one, h.mul_mul_eq]
  · calc
      (V * B * Uᴴ) * (U * A * Vᴴ) * (V * B * Uᴴ) =
          V * (B * (Uᴴ * U) * A * (Vᴴ * V) * B) * Uᴴ := by
            simp only [Matrix.mul_assoc]
      _ = V * B * Uᴴ := by
        rw [hU, hV, Matrix.mul_one, Matrix.mul_one, h.inv_mul_inv_eq]
  · have he : (U * A * Vᴴ) * (V * B * Uᴴ) = U * (A * B) * Uᴴ := by
      calc
        _ = U * (A * (Vᴴ * V) * B) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
    rw [he]
    calc
      (U * (A * B) * Uᴴ)ᴴ = U * (A * B)ᴴ * Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = U * (A * B) * Uᴴ := by rw [h.conjTranspose_mul_eq]
  · have he : (V * B * Uᴴ) * (U * A * Vᴴ) = V * (B * A) * Vᴴ := by
      calc
        _ = V * (B * (Uᴴ * U) * A) * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]
    rw [he]
    calc
      (V * (B * A) * Vᴴ)ᴴ = V * (B * A)ᴴ * Vᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = V * (B * A) * Vᴴ := by rw [h.conjTranspose_inv_mul_eq]

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
theorem mulVec_eq_self_iff (h : IsMoorePenroseInverse A B) (x : m → 𝕜) :
    (A * B) *ᵥ x = x ↔ ∃ y : n → 𝕜, A *ᵥ y = x := by
  constructor
  · intro hx
    exact ⟨B *ᵥ x, by rw [Matrix.mulVec_mulVec]; exact hx⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_mulVec, h.mul_mul_eq]

/-- The image of `A B` equals the image of `A`: the Hermitian idempotent
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
Gram matrix of the inverse: `(AᴴA)⁺ = A⁺A⁺ᴴ`. This identity holds at every rank.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem conjTranspose_mul_self (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse (Aᴴ * A) (B * Bᴴ) := by
  have hCG : (B * Bᴴ) * (Aᴴ * A) = B * A := by
    calc
      _ = B * (A * B)ᴴ * A := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B * (A * B) * A := by rw [h.conjTranspose_mul_eq]
      _ = (B * A * B) * A := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [h.inv_mul_inv_eq]
  have hGC : (Aᴴ * A) * (B * Bᴴ) = B * A := by
    calc
      _ = ((B * Bᴴ) * (Aᴴ * A))ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = (B * A)ᴴ := by rw [hCG]
      _ = B * A := h.conjTranspose_inv_mul_eq
  constructor
  · calc
      _ = (Aᴴ * A) * ((B * Bᴴ) * (Aᴴ * A)) := Matrix.mul_assoc _ _ _
      _ = (Aᴴ * A) * (B * A) := by rw [hCG]
      _ = Aᴴ * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = Aᴴ * A := by rw [h.mul_mul_eq]
  · calc
      _ = (B * A) * (B * Bᴴ) := by rw [hCG]
      _ = (B * A * B) * Bᴴ := by simp only [Matrix.mul_assoc]
      _ = B * Bᴴ := by rw [h.inv_mul_inv_eq]
  · rw [hGC]
    exact h.conjTranspose_inv_mul_eq
  · rw [hCG]
    exact h.conjTranspose_inv_mul_eq

end IsMoorePenroseInverse

end NLAlib
