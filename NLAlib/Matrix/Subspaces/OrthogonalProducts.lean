import NLAlib.Matrix.Subspaces.Projections
/-!
# Matrices with orthonormal columns: products, relabelling, rank and isometry

The generic API of `HasOrthonormalCols Q` (`Qᴴ Q = I`) beyond projectors and residuals
(`NLAlib.Matrix.Subspaces.Projections`), over `[RCLike 𝕜]`:

* closure: products (`HasOrthonormalCols.mul`), adjoints of square frames
  (`HasOrthonormalCols.conjTranspose`, `HasOrthonormalCols.mul_conjTranspose_self`), column
  selections (`HasOrthonormalCols.submatrix_cols`) and relabelling of rows and columns
  (`HasOrthonormalCols.reindex`);
* left multiplication by a frame preserves rank (`rank_isometry_mul_eq`);
* the induced Euclidean linear isometry (`HasOrthonormalCols.toLinearIsometry`);
* column identities: `(Qᴴ Q)ᵢⱼ = ⟨qᵢ, qⱼ⟩`, `Q v = ∑ⱼ vⱼ qⱼ`, orthonormality and linear
  independence of the columns, and the Euclidean inner product as a dot product
  (`inner_eq_star_dotProduct_ofLp`).

Horn–Johnson 2013, §2.1 and §0.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A product of column isometries is a column isometry. Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.mul {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p] {P : Matrix m n 𝕜} {Q : Matrix n p 𝕜}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) : HasOrthonormalCols (P * Q) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P Q,
    hP.conjTranspose_mul_self, Matrix.one_mul, hQ.conjTranspose_mul_self]

/-- A square matrix with orthonormal columns is unitary: `U Uᴴ = I`. Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.mul_conjTranspose_self {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : U * Uᴴ = 1 :=
  mul_eq_one_comm.mp hU.conjTranspose_mul_self

/-- The adjoint of a square unitary matrix is unitary, including empty matrices.
Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : HasOrthonormalCols Uᴴ := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
  exact hU.mul_conjTranspose_self

/-- A square matrix with orthonormal columns is invertible, with inverse `Uᴴ`.
Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : IsUnit U :=
  ⟨⟨U, Uᴴ, hU.mul_conjTranspose_self, hU.conjTranspose_mul_self⟩, rfl⟩

/-- The inverse of a square matrix with orthonormal columns is its adjoint.
Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.inv_eq_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : U⁻¹ = Uᴴ :=
  Matrix.inv_eq_left_inv hU.conjTranspose_mul_self

/-- Selecting distinct columns of an orthonormal frame preserves orthonormality.
Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.submatrix_cols {m n r : Type*} [Fintype m] [Fintype n]
    [Fintype r] [DecidableEq n] [DecidableEq r] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (e : r ↪ n) : HasOrthonormalCols (Q.submatrix id e) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_submatrix]
  have h := Matrix.submatrix_mul_equiv Qᴴ Q e (Equiv.refl m) e
  simp only [Equiv.coe_refl] at h
  rw [h, hQ.conjTranspose_mul_self]
  ext i j
  simp [Matrix.one_apply, e.injective.eq_iff]

/-- Relabelling rows and columns preserves orthonormal columns, including empty index types.
Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.reindex {m n p q : Type*} [Fintype m] [Fintype p] [DecidableEq n]
    [DecidableEq q] {U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (em : m ≃ p) (en : n ≃ q) :
    HasOrthonormalCols (U.reindex em en) := by
  rw [HasOrthonormalCols]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hU.conjTranspose_mul_self, Matrix.submatrix_one_equiv]

/-- A block-diagonal matrix with orthonormal-column blocks has orthonormal columns.
Horn–Johnson 2013, §2.1. -/
theorem HasOrthonormalCols.fromBlocks_diagonal {p q r s : Type*} [Fintype p] [Fintype q]
    [Fintype r] [Fintype s] [DecidableEq q] [DecidableEq s]
    {A : Matrix p q 𝕜} {B : Matrix r s 𝕜} (hA : HasOrthonormalCols A)
    (hB : HasOrthonormalCols B) : HasOrthonormalCols (Matrix.fromBlocks A 0 0 B) := by
  rw [HasOrthonormalCols]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    hA.conjTranspose_mul_self, hB.conjTranspose_mul_self, Matrix.fromBlocks_one]

/-- The identity has orthonormal columns. -/
theorem hasOrthonormalCols_one {n : Type*} [Fintype n] [DecidableEq n] :
    HasOrthonormalCols (1 : Matrix n n 𝕜) := by
  simp [HasOrthonormalCols]

/-- A column isometry preserves matrix rank, including rectangular and empty isometries.
Horn–Johnson 2013, §0.4. -/
theorem rank_isometry_mul_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    {Q : Matrix m p 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    (Q * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have hBack : Qᴴ * (Q * A) = A := by
    rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul]
  calc
    A.rank = (Qᴴ * (Q * A)).rank := congrArg Matrix.rank hBack.symm
    _ ≤ (Q * A).rank := Matrix.rank_mul_le_right _ _

/-- A matrix with orthonormal columns defines a linear isometry of the corresponding Euclidean
spaces (the map `Matrix.toEuclideanLin Q`); for a square unitary matrix this is a unitary
Euclidean isometry. Horn–Johnson 2013, §2.1. -/
def HasOrthonormalCols.toLinearIsometry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    EuclideanSpace 𝕜 n →ₗᵢ[𝕜] EuclideanSpace 𝕜 m where
  toLinearMap := Q.toEuclideanLin
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 (Q *ᵥ x.ofLp) : EuclideanSpace 𝕜 m)‖ ^ 2 = ‖x‖ ^ 2
    rw [norm_toLp_sq_eq_re_star_dotProduct,
      star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ]
    have h := norm_toLp_sq_eq_re_star_dotProduct (𝕜 := 𝕜) x.ofLp
    simp only [WithLp.toLp_ofLp] at h
    exact h.symm

/-! ### Columns of a frame -/

section Columns

variable {n : Type*} [Fintype n]

/-- `(Qᴴ Q)_ij = ⟨q_i, q_j⟩ = star q_i ⬝ q_j`. Helper for `arnoldi-def`. -/
theorem conjTranspose_mul_self_apply {k : Type*} (Q : Matrix n k 𝕜) (i j : k) :
    (Qᴴ * Q) i j = star (Q.col i) ⬝ᵥ Q.col j := by
  simp [Matrix.mul_apply, dotProduct, Matrix.col]

omit [Fintype n] in
/-- `Q v = ∑ⱼ vⱼ qⱼ`. Helper for `arnoldi-def`. -/
theorem mulVec_eq_sum_smul_col {k : Type*} [Fintype k] (Q : Matrix n k 𝕜) (v : k → 𝕜) :
    Q *ᵥ v = ∑ j, v j • Q.col j := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.col, mul_comm]

/-- Columns of a matrix with orthonormal columns: `⟨q_i, q_j⟩ = δ_ij`. -/
theorem HasOrthonormalCols.star_col_dotProduct_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k 𝕜} (hQ : HasOrthonormalCols Q) (i j : k) :
    star (Q.col i) ⬝ᵥ Q.col j = if i = j then 1 else 0 := by
  rw [← conjTranspose_mul_self_apply, hQ.conjTranspose_mul_self, Matrix.one_apply]

/-- Orthonormal columns are linearly independent. Helper for `graded-krylov-basis-def`. -/
theorem HasOrthonormalCols.linearIndependent_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k 𝕜} (hQ : HasOrthonormalCols Q) : LinearIndependent 𝕜 Q.col := by
  rw [← Matrix.mulVec_injective_iff]
  intro x y hxy
  have h := congrArg (fun v => Qᴴ *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec] using h

/-- The Euclidean inner product is the (conjugate-linear in the first slot) dot product of the
coordinates: `⟨x, y⟩ = star x ⬝ y`. Helper for `arnoldi-def`. -/
theorem inner_eq_star_dotProduct_ofLp (x y : EuclideanSpace 𝕜 n) :
    inner 𝕜 x y = star x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

end Columns

end NLAlib
