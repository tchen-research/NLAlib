import NLAlib.Matrix.Perturbation.LeastSquaresGeometry
/-!
# Native least-squares predicates and Euclidean norms

Transport the ordinary-coordinate least-squares API to Euclidean vectors.
Trefethen–Bau, Lecture 11; Higham, Theorem 20.1.
Supports `least-squares-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq n] in
/-- A coordinate squared norm is the squared Euclidean norm.
Mathlib's Euclidean norm identity; supports least-squares transport. -/
theorem dotProduct_ofLp_self_eq_norm_sq (v : EuclideanSpace ℝ n) :
    v.ofLp ⬝ᵥ v.ofLp=‖v‖^2 := by
  simpa only [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq v).symm

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- The native least-squares predicate is equivalent to Euclidean residual
norm minimization. Trefethen–Bau, Lecture 11; no rank assumption is needed. -/
theorem isLeastSquaresSolution_iff_euclidean_norm_min (A : Matrix m n ℝ)
    (b : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    IsLeastSquaresSolution A b.ofLp x.ofLp ↔
      ∀ z : EuclideanSpace ℝ n, ‖b-A.toEuclideanLin x‖ ≤ ‖b-A.toEuclideanLin z‖ := by
  constructor
  · intro h z
    exact h z.ofLp
  · intro h z
    exact h (WithLp.toLp 2 z)

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq n] in
/-- The Euclidean Moore–Penrose solution satisfies the native
least-squares predicate. Trefethen–Bau, Lecture 11; every rank is included. -/
theorem isLeastSquaresSolution_toEuclideanLin_pinv (A : Matrix m n ℝ)
    (b : EuclideanSpace ℝ m) :
    IsLeastSquaresSolution A b.ofLp ((moorePenroseInverse A).toEuclideanLin b).ofLp := by
  exact isLeastSquaresSolution_moorePenroseInverse_mulVec A b.ofLp

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq n] in
/-- Full column rank makes the Euclidean Moore–Penrose solution the
unique solution of the native least-squares predicate. Trefethen–Bau, Lecture 11. -/
theorem isLeastSquaresSolution_eq_toEuclideanLin_pinv {A : Matrix m n ℝ}
    (hA : A.rank=Fintype.card n) (b : EuclideanSpace ℝ m) {z : n → ℝ}
    (hz : IsLeastSquaresSolution A b.ofLp z) :
    z=((moorePenroseInverse A).toEuclideanLin b).ofLp :=
  (isLeastSquaresSolution_iff_eq_moorePenroseInverse_mulVec hA b.ofLp z).mp hz

end NLAlib
