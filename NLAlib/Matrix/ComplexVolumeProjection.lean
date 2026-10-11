import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Actual complex column-range orthogonal projectors

The projector is Mathlib's genuine Hilbert orthogonal projection onto the
range of the column operator, transported back to a matrix. It is defined
at every rank and shape. Source: `sa:volume`; supports `volume-sampling`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical Matrix InnerProductSpace ComplexOrder
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The complex column range as an actual Euclidean Hilbert subspace.
Source: the column span in operator re-derivation `sa:volume`. -/
def complexColumnSpace (B : Matrix m n ℂ) : Submodule ℂ (EuclideanSpace ℂ m) :=
  LinearMap.range (Matrix.toEuclideanLin B)

/-- The actual complex orthogonal projector onto the column range, including
dependent columns and the empty span. Source: `sa:volume`. -/
def complexColumnProjector (B : Matrix m n ℂ) : Matrix m m ℂ :=
  Matrix.toEuclideanLin.symm (complexColumnSpace B).starProjection.toLinearMap

/-- The matrix projector is precisely Mathlib's genuine Hilbert projection.
Source: `sa:volume`, actual projector bridge. -/
theorem toEuclideanLin_complexColumnProjector (B : Matrix m n ℂ) :
    Matrix.toEuclideanLin (complexColumnProjector B) =
      (complexColumnSpace B).starProjection.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

omit [Fintype m] [DecidableEq m] in
/-- The operator range is exactly the span of the actual complex columns.
Source: `sa:volume`, no real embedding restriction. -/
theorem complexColumnSpace_eq_span_columns (B : Matrix m n ℂ) :
    complexColumnSpace B = Submodule.span ℂ
      (Set.range (fun j => (WithLp.toLp 2 (B.col j) : EuclideanSpace ℂ m))) := by
  change LinearMap.range (Matrix.toEuclideanLin B) = _
  rw [← Submodule.map_top, ← (EuclideanSpace.basisFun n ℂ).toBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  have hf : (Matrix.toEuclideanLin B) ∘ (EuclideanSpace.basisFun n ℂ).toBasis =
      (fun j => (WithLp.toLp 2 (B.col j) : EuclideanSpace ℂ m)) := by
    funext j
    simp only [Function.comp_def, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.ofLp_single,
      Matrix.mulVec_single]
    simp
  exact congrArg (Submodule.span ℂ) (congrArg Set.range hf)

/-- The actual complex column projector is Hermitian.
Source: the Hilbert orthogonal projection, `sa:volume`. -/
theorem complexColumnProjector_isHermitian (B : Matrix m n ℂ) :
    (complexColumnProjector B).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  rw [toEuclideanLin_complexColumnProjector]
  exact (complexColumnSpace B).starProjection_isSymmetric

/-- The actual complex column projector is idempotent.
Source: the Hilbert orthogonal projection, `sa:volume`. -/
theorem complexColumnProjector_mul_self (B : Matrix m n ℂ) :
    complexColumnProjector B * complexColumnProjector B = complexColumnProjector B := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, toEuclideanLin_complexColumnProjector]
  have hh := congrArg ContinuousLinearMap.toLinearMap
    (complexColumnSpace B).isIdempotentElem_starProjection
  exact hh

/-- The actual projector fixes every input column at any rank.
Source: `sa:volume`, selected-column preservation. -/
theorem complexColumnProjector_mul (B : Matrix m n ℂ) :
    complexColumnProjector B * B = B := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, toEuclideanLin_complexColumnProjector]
  apply LinearMap.ext
  intro x
  exact (Submodule.starProjection_eq_self_iff (K := complexColumnSpace B)).mpr ⟨x, rfl⟩

/-- The range of the projector is exactly the column space.
Source: `sa:volume`, actual range certificate. -/
theorem range_toEuclideanLin_complexColumnProjector (B : Matrix m n ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (complexColumnProjector B)) = complexColumnSpace B := by
  rw [toEuclideanLin_complexColumnProjector]
  exact Submodule.range_starProjection _

omit [DecidableEq m] in
/-- Matrix rank equals the genuine Hilbert column-range dimension.
Source: coordinate invariance of rank; supports `sa:volume`. -/
theorem rank_eq_finrank_complexColumnSpace (B : Matrix m n ℂ) :
    B.rank = Module.finrank ℂ (complexColumnSpace B) := by
  unfold complexColumnSpace
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin B
    (EuclideanSpace.basisFun m ℂ).toBasis (EuclideanSpace.basisFun n ℂ).toBasis

/-- The actual column projector has exactly the input rank.
Source: `sa:volume`, valid at every rank and rectangular shape. -/
theorem rank_complexColumnProjector (B : Matrix m n ℂ) :
    (complexColumnProjector B).rank = B.rank := by
  rw [rank_eq_finrank_complexColumnSpace, rank_eq_finrank_complexColumnSpace]
  rw [show complexColumnSpace (complexColumnProjector B) = complexColumnSpace B from
    range_toEuclideanLin_complexColumnProjector B]

/-- The row-space projector built from the genuine complex adjoint fixes the
matrix on the right. Source: `sa:volume`, optimal-tail helper. -/
theorem mul_complexColumnProjector_conjTranspose (B : Matrix m n ℂ) :
    B * complexColumnProjector Bᴴ = B := by
  have hh := congrArg Matrix.conjTranspose (complexColumnProjector_mul Bᴴ)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (complexColumnProjector_isHermitian Bᴴ).eq] using hh

end NLAlib
