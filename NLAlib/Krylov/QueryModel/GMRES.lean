import NLAlib.Krylov.QueryModel.Powers
import NLAlib.Krylov.Solvers.GMRESIterate

/-!
# Query realization of real and complex GMRES

The `q` responses `A r₀, ..., A^q r₀` determine both the Krylov generator matrix
and its image. Solving the resulting finite least-squares problem is free in the
matrix-vector query model. This exact-arithmetic realization is not a numerical
stability claim about implementing GMRES in the power basis.

The input residual is supplied explicitly. A zero initial guess needs no initial
matrix product; for a general initial guess computing `c - A x₀` costs another query.
Source: Saad--Schultz (1986), Section 2; Saad (2003), Section 6.5.
atlas: matvec-query-model (partial)
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The power-basis GMRES solve from its initial data and `q` matrix-vector responses.
The algorithm contains no reference to the matrix. -/
def gmresQueryAlgorithm (x₀ r₀ : n → 𝕜) (q : ℕ) :
    QueryAlgorithm (n → 𝕜) (n → 𝕜) q (n → 𝕜) :=
  (powerQueryAlgorithm r₀ q).withOutput fun h =>
    x₀ + krylovMatrixFromTranscript r₀ h *ᵥ
      (moorePenroseInverse (fun i j => h j i) *ᵥ r₀)

/-- With the initial residual supplied, `q` queries compute precisely the concrete
GMRES iterate, over either real or complex scalars and at every rank.
atlas: matvec-query-model (partial) -/
theorem run_gmresQueryAlgorithm (A : Matrix n n 𝕜) (c x₀ r₀ : n → 𝕜)
    (hr : r₀ = c - A *ᵥ x₀) (q : ℕ) :
    (gmresQueryAlgorithm x₀ r₀ q).run (A *ᵥ ·) = gmresIterate A c x₀ q := by
  rw [gmresQueryAlgorithm, QueryAlgorithm.run_withOutput,
    krylovMatrixFromTranscript_eq, responseMatrix_powerQueryAlgorithm, hr]
  rfl

/-- Starting from zero, `q` queries suffice for the actual `q`-th GMRES iterate.
This equality includes early Krylov breakdown and the zero right-hand side.
atlas: matvec-query-model (partial) -/
theorem run_gmresQueryAlgorithm_zero (A : Matrix n n 𝕜) (c : n → 𝕜) (q : ℕ) :
    (gmresQueryAlgorithm 0 c q).run (A *ᵥ ·) = gmresIterate A c 0 q :=
  run_gmresQueryAlgorithm A c 0 c (by simp) q

/-- GMRES with a general initial guess: one query computes `A x₀`, then `q` queries
construct the Krylov least-squares problem. The charged budget is `q + 1`. -/
def gmresInitializedQueryAlgorithm (c x₀ : n → 𝕜) (q : ℕ) :
    QueryAlgorithm (n → 𝕜) (n → 𝕜) (q + 1) (n → 𝕜) :=
  QueryAlgorithm.prependQuery x₀ (fun response => gmresQueryAlgorithm x₀ (c - response) q)

/-- The initial-residual computation is included in the query implementation for a
general initial guess.
atlas: matvec-query-model (partial) -/
theorem run_gmresInitializedQueryAlgorithm (A : Matrix n n 𝕜) (c x₀ : n → 𝕜) (q : ℕ) :
    (gmresInitializedQueryAlgorithm c x₀ q).run (A *ᵥ ·) = gmresIterate A c x₀ q := by
  rw [gmresInitializedQueryAlgorithm, QueryAlgorithm.run_prependQuery]
  exact run_gmresQueryAlgorithm A c x₀ _ rfl q

end NLAlib
