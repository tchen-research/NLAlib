import NLAlib.Matrix.Subspaces.Projections
/-!
# Matrices with orthonormal columns: products, relabelling, rank and isometry

The generic API of `HasOrthonormalCols Q` (`Qᵀ Q = I`) beyond projectors and residuals
(`NLAlib.Matrix.Subspaces.Projections`):

* closure: products (`HasOrthonormalCols.mul`), transposes of square frames
  (`HasOrthonormalCols.transpose`), column selections (`HasOrthonormalCols.submatrix_cols`) and
  relabelling of rows and columns (`HasOrthonormalCols.reindex`);
* left multiplication by a frame preserves rank (`rank_isometry_mul_eq`);
* the induced Euclidean linear isometry (`HasOrthonormalCols.toLinearIsometry`);
* column identities: `(Qᵀ Q)ᵢⱼ = qᵢ ⬝ qⱼ`, `Q v = ∑ⱼ vⱼ qⱼ`,
  orthonormality and linear independence of the columns, and the Euclidean inner product as a
  dot product (`inner_eq_dotProduct_ofLp`).

Horn–Johnson 2013, §2.1 and §0.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A product of column isometries is a column isometry. Horn–Johnson §2.1. -/
theorem HasOrthonormalCols.mul {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p] {P : Matrix m n ℝ} {Q : Matrix n p ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) : HasOrthonormalCols (P * Q) := by
  change (P * Q)ᵀ * (P * Q) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P Q,
    hP, Matrix.one_mul, hQ]

/-- The transpose of a square orthogonal matrix is orthogonal, including
empty matrices. Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.transpose {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℝ} (hU : HasOrthonormalCols U) : HasOrthonormalCols Uᵀ := by
  change Uᵀᵀ * Uᵀ = 1
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.mp hU

/-- Selecting distinct columns of an orthonormal frame preserves orthonormality.
This is the finite frame API used by the attaining Ky Fan optimizers. -/
theorem HasOrthonormalCols.submatrix_cols {m n r : Type*} [Fintype m] [Fintype n]
    [Fintype r] [DecidableEq n] [DecidableEq r] {Q : Matrix m n ℝ}
    (hQ : HasOrthonormalCols Q) (e : r ↪ n) : HasOrthonormalCols (Q.submatrix id e) := by
  change (Q.submatrix id e)ᵀ * Q.submatrix id e = 1
  rw [Matrix.transpose_submatrix]
  have h := Matrix.submatrix_mul_equiv Qᵀ Q e (Equiv.refl m) e
  simp only [Equiv.coe_refl] at h
  rw [h, hQ]
  ext i j
  simp [Matrix.one_apply, e.injective.eq_iff]

/-- Relabelling rows and columns preserves orthonormal columns, including
empty index types. Source: Horn–Johnson, §5.6, permutation of Gram coordinates;
supports `ose-def` and finite-index sparse sampling. -/
theorem HasOrthonormalCols.reindex {m n p q : Type*} [Fintype m] [Fintype p] [DecidableEq n]
    [DecidableEq q] {U : Matrix m n ℝ} (hU : HasOrthonormalCols U) (em : m ≃ p) (en : n ≃ q) :
    HasOrthonormalCols (U.reindex em en) := by
  change (U.reindex em en)ᵀ * (U.reindex em en) = 1
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hU, Matrix.submatrix_one_equiv]

/-- A column isometry preserves matrix rank, including rectangular and empty
isometries. Horn–Johnson 2013, Section 0.4; RRQR transport helper. -/
theorem rank_isometry_mul_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    {Q : Matrix m p ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix p n ℝ) :
    (Q * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have hBack : Qᵀ * (Q * A) = A := by
    rw [← Matrix.mul_assoc, show Qᵀ * Q = 1 from hQ, Matrix.one_mul]
  calc
    A.rank = (Qᵀ * (Q * A)).rank := congrArg Matrix.rank hBack.symm
    _ ≤ (Q * A).rank := Matrix.rank_mul_le_right _ _

/-- A rectangular real matrix with orthonormal columns defines an actual
linear isometry of the corresponding Euclidean spaces (the map `Matrix.toEuclideanLin Q`); for a
square orthogonal matrix this is the orthogonal Euclidean isometry. Supports QR. -/
def HasOrthonormalCols.toLinearIsometry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n ℝ} (hQ : HasOrthonormalCols Q) :
    EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ m where
  toLinearMap := Q.toEuclideanLin
  norm_map' x := by
    rw [norm_eq_sqrt_dotProduct, norm_eq_sqrt_dotProduct]
    change Real.sqrt ((Q *ᵥ x.ofLp) ⬝ᵥ (Q *ᵥ x.ofLp)) = Real.sqrt (x.ofLp ⬝ᵥ x.ofLp)
    rw [mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ]

/-! ### Columns of a frame -/

section Columns

variable {n : Type*} [Fintype n]

/-- `(Qᵀ Q)_ij = q_i ⬝ q_j`. Helper for `arnoldi-def`. -/
theorem transpose_mul_self_apply {k : Type*} (Q : Matrix n k ℝ) (i j : k) :
    (Qᵀ * Q) i j = Q.col i ⬝ᵥ Q.col j := by
  simp [Matrix.mul_apply, dotProduct, Matrix.col]

omit [Fintype n] in
/-- `Q v = ∑ⱼ vⱼ qⱼ`. Helper for `arnoldi-def`. -/
theorem mulVec_eq_sum_smul_col {k : Type*} [Fintype k] (Q : Matrix n k ℝ) (v : k → ℝ) :
    Q *ᵥ v = ∑ j, v j • Q.col j := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.col, mul_comm]

/-- Columns of a matrix with orthonormal columns: `q_i ⬝ q_j = δ_ij`. -/
theorem HasOrthonormalCols.col_dotProduct_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (i j : k) :
    Q.col i ⬝ᵥ Q.col j = if i = j then 1 else 0 := by
  rw [← transpose_mul_self_apply, show Qᵀ * Q = 1 from hQ, Matrix.one_apply]

/-- Orthonormal columns are linearly independent. Helper for `graded-krylov-basis-def`. -/
theorem HasOrthonormalCols.linearIndependent_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) : LinearIndependent ℝ Q.col := by
  rw [← Matrix.mulVec_injective_iff]
  intro x y hxy
  have h := congrArg (fun v => Qᵀ *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec] using h

/-- The real inner product on `EuclideanSpace ℝ n` is the dot product of the coordinates.
Helper for `arnoldi-def`. -/
theorem inner_eq_dotProduct_ofLp (x y : EuclideanSpace ℝ n) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

end Columns

end NLAlib
