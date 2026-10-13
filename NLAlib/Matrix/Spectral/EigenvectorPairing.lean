import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Left and right eigenvectors

Algebraic pairing identities, rank-one invariant projectors, and transport
under similarity. A left eigenvector is represented by its row coordinates;
over the complex field take the row `star y` to recover `y*`.
Source: Horn–Johnson (2013), §1.4; atlas `left-right-eigenvectors`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {K : Type*} [Field K]

/-- Every spectral point of a matrix has a nonzero right eigenvector.
Source: Horn–Johnson (2013), Definition 1.4.6; follows from the determinant
criterion and applies over an arbitrary field. -/
theorem exists_mulVec_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ x : n → K, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  have hdet : (μ • (1 : Matrix n n K) - A).det = 0 := by
    simpa only [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ).eq_zero
  obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨x, hx, ?_⟩
  exact (sub_eq_zero.mp (by simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] using hAx)).symm

/-- Every spectral point also has a nonzero left eigenvector.
Source: Horn–Johnson (2013), Definition 1.4.6; transpose preserves the
characteristic polynomial, so no normality is required. -/
theorem exists_vecMul_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ y : n → K, y ≠ 0 ∧ y ᵥ* A = μ • y := by
  have htrans : μ ∈ spectrum K Aᵀ := by
    simpa only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose] using hμ
  obtain ⟨y, hy, hAy⟩ := exists_mulVec_eq_smul_of_mem_spectrum htrans
  exact ⟨y, hy, by simpa only [Matrix.mulVec_transpose] using hAy⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Left and right eigenvectors at different eigenvalues are biorthogonal.
Source: Horn–Johnson (2013), Observation 1.4.6a; `y` denotes the left row,
which may be `star y₀` for a complex column eigenvector `y₀`.
atlas: left-right-eigenvectors -/
theorem dotProduct_eq_zero_of_left_right_eigenvalues_ne {A : Matrix n n K}
    {x y : n → K} {α μ : K} (hx : A *ᵥ x = α • x)
    (hy : y ᵥ* A = μ • y) (hαμ : α ≠ μ) : y ⬝ᵥ x = 0 := by
  have hpair : α * (y ⬝ᵥ x) = μ * (y ⬝ᵥ x) := by
    calc
      _ = y ⬝ᵥ (A *ᵥ x) := by rw [hx, dotProduct_smul]; rfl
      _ = (y ᵥ* A) ⬝ᵥ x := Matrix.dotProduct_mulVec y A x
      _ = _ := by rw [hy, smul_dotProduct]; rfl
  exact (mul_eq_mul_right_iff.mp hpair).resolve_left hαμ

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- A nonzero right column and nonzero left row give a nonzero outer product.
Source: Horn–Johnson (2013), §1.4; the assertion includes rectangular shapes. -/
theorem vecMulVec_ne_zero {x : m → K} {y : n → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    Matrix.vecMulVec x y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  intro hxy
  have heq := congrArg (fun M : Matrix m n K => M i j) hxy
  exact mul_ne_zero hi hj heq

omit [DecidableEq m] [DecidableEq n] in
/-- A common eigenvalue produces a rank-one rectangular intertwiner.
Source: Horn–Johnson (2013), Theorem 2.4.4.1, converse Sylvester obstruction. -/
theorem mul_vecMulVec_eq_vecMulVec_mul {A : Matrix m m K} {B : Matrix n n K}
    {x : m → K} {y : n → K} {μ : K} (hx : A *ᵥ x = μ • x)
    (hy : y ᵥ* B = μ • y) :
    A * Matrix.vecMulVec x y = Matrix.vecMulVec x y * B := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hx, hy]
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq m] [DecidableEq n] in
/-- The normalized outer product of paired left and right eigenvectors is
idempotent. Source: Horn–Johnson (2013), Theorem 1.4.7; nonzero pairing is
the exact side condition, without a simplicity assumption.
atlas: left-right-eigenvectors (partial) -/
theorem normalized_vecMulVec_mul_self {x y : n → K} (hpair : y ⬝ᵥ x ≠ 0) :
    ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) *
      ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) =
        (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul, smul_smul]
  congr 1
  field_simp

omit [DecidableEq m] [DecidableEq n] in
/-- The paired rank-one projector commutes with the matrix and both products
equal the eigenvalue times that projector. Source: Horn–Johnson (2013),
Theorem 1.4.7; without simplicity it splits off one invariant line.
atlas: left-right-eigenvectors (partial) -/
theorem mul_normalized_vecMulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hx : A *ᵥ x = μ • x) (hy : y ᵥ* A = μ • y) :
    A * ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) =
      μ • ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) ∧
    ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) * A =
      μ • ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) := by
  constructor
  · rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hx, Matrix.smul_vecMulVec,
      smul_smul, smul_smul, mul_comm]
  · rw [Matrix.smul_mul, Matrix.vecMulVec_mul, hy]
    ext i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring

omit [DecidableEq m] [DecidableEq n] in
/-- Similarity transports a right eigenvector by the similarity matrix.
Source: Horn–Johnson (2013), Theorem 2.4.11.1.
atlas: left-right-eigenvectors -/
theorem mulVec_eigenvector_of_intertwines {A B S : Matrix n n K} {x : n → K}
    {μ : K} (hS : A * S = S * B) (hx : B *ᵥ x = μ • x) :
    A *ᵥ (S *ᵥ x) = μ • (S *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, hS, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

omit [DecidableEq m] [DecidableEq n] in
/-- Similarity transports a left row eigenvector by right multiplication
with the inverse similarity matrix. Source: Horn–Johnson (2013),
Theorem 2.4.11.1; for complex columns this is inverse conjugate transpose.
atlas: left-right-eigenvectors -/
theorem vecMul_eigenvector_of_intertwines {A B S : Matrix n n K} {y : n → K}
    {μ : K} (hS : S * A = B * S) (hy : y ᵥ* B = μ • y) :
    (y ᵥ* S) ᵥ* A = μ • (y ᵥ* S) := by
  rw [Matrix.vecMul_vecMul, hS, ← Matrix.vecMul_vecMul, hy, Matrix.smul_vecMul]

end NLAlib
