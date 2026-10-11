import NLAlib.Matrix.ComplexProjectionBounds

/-!
# Nested actual complex column projectors

Containment of one complex column range in another makes the projectors compose
and gives monotone spectral and Frobenius residual errors. Source: Hilbert orthogonal
projection; manuscript `sa:filter`, block Krylov specialization.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]

/-- Reproducing the inner columns makes actual complex column projectors compose.
Source: Hilbert range projection; manuscript `sa:filter`. -/
theorem complexColumnProjector_mul_eq_of_mul_eq
    (Q : Matrix m k ℂ) (Y : Matrix m l ℂ) (h : complexColumnProjector Q * Y = Y) :
    complexColumnProjector Q * complexColumnProjector Y = complexColumnProjector Y := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same]
  apply LinearMap.ext
  intro x
  have hy : Matrix.toEuclideanLin (complexColumnProjector Y) x ∈ complexColumnSpace Y := by
    rw [← range_toEuclideanLin_complexColumnProjector Y]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hy
  have hh := congrArg (fun M : Matrix m l ℂ => Matrix.toEuclideanLin M z) h
  rw [Matrix.toLpLin_mul_same] at hh
  change Matrix.toEuclideanLin (complexColumnProjector Q)
      (Matrix.toEuclideanLin (complexColumnProjector Y) x) =
    Matrix.toEuclideanLin (complexColumnProjector Y) x
  rw [← hz]
  exact hh

/-- For complex orthonormal columns, the actual Hilbert column projector equals
the familiar matrix `Q Qᴴ`. Source: manuscript `sa:filter`, projector definition;
standard orthogonal projection uniqueness. -/
theorem complexColumnProjector_eq_mul_conjTranspose (Q : Matrix m k ℂ)
    (hQ : Qᴴ * Q = 1) : complexColumnProjector Q = Q * Qᴴ := by
  have hprod : (Q * Qᴴ) * complexColumnProjector Q = complexColumnProjector Q := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same]
    apply LinearMap.ext
    intro x
    have hy : Matrix.toEuclideanLin (complexColumnProjector Q) x ∈ complexColumnSpace Q := by
      rw [← range_toEuclideanLin_complexColumnProjector Q]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hy
    change Matrix.toEuclideanLin (Q * Qᴴ)
        (Matrix.toEuclideanLin (complexColumnProjector Q) x) =
      Matrix.toEuclideanLin (complexColumnProjector Q) x
    rw [← hz]
    have hm : (Q * Qᴴ) * Q = Q := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
    have hh := congrArg (fun M : Matrix m k ℂ => Matrix.toEuclideanLin M z) hm
    rw [Matrix.toLpLin_mul_same] at hh
    exact hh
  have hadj : Qᴴ * complexColumnProjector Q = Qᴴ := by
    have hh := congrArg Matrix.conjTranspose (complexColumnProjector_mul Q)
    simpa only [Matrix.conjTranspose_mul, (complexColumnProjector_isHermitian Q).eq] using hh
  calc complexColumnProjector Q = (Q * Qᴴ) * complexColumnProjector Q := hprod.symm
    _ = Q * Qᴴ := by rw [Matrix.mul_assoc, hadj]

/-- A containing actual complex column space has no larger spectral residual.
Source: projection contraction; manuscript `sa:filter`, block Krylov specialization. -/
theorem norm_sub_complexColumnProjector_mul_le_of_mul_eq
    (Q : Matrix m k ℂ) (Y : Matrix m l ℂ)
    (h : complexColumnProjector Q * Y = Y) (A : Matrix m n ℂ) :
    ‖A - complexColumnProjector Q * A‖ ≤ ‖A - complexColumnProjector Y * A‖ := by
  have hp := complexColumnProjector_mul_eq_of_mul_eq Q Y h
  have he : A - complexColumnProjector Q * A =
      (A - complexColumnProjector Y * A) -
        complexColumnProjector Q * (A - complexColumnProjector Y * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hp]
    abel
  rw [he]
  exact norm_sub_complexColumnProjector_mul_le _ _

section Frobenius
open scoped Matrix.Norms.Frobenius

omit [DecidableEq n] in
/-- A containing actual complex column space has no larger squared Frobenius
residual. Source: projection contraction; manuscript `sa:filter`. -/
theorem frobenius_norm_sub_complexColumnProjector_mul_sq_le_of_mul_eq
    (Q : Matrix m k ℂ) (Y : Matrix m l ℂ)
    (h : complexColumnProjector Q * Y = Y) (A : Matrix m n ℂ) :
    ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖A - complexColumnProjector Y * A‖ ^ 2 := by
  have hp := complexColumnProjector_mul_eq_of_mul_eq Q Y h
  have he : A - complexColumnProjector Q * A =
      (A - complexColumnProjector Y * A) -
        complexColumnProjector Q * (A - complexColumnProjector Y * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hp]
    abel
  rw [he]
  exact frobenius_norm_sub_complexColumnProjector_mul_sq_le _ _

end Frobenius
end NLAlib
