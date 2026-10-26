import NLAlib.Krylov.QueryModel.Iteration
import NLAlib.Krylov.Processes.LanczosRecurrence
import NLAlib.Krylov.Solvers.CGRecurrence

/-!
# Matrix-vector query realizations of Lanczos and conjugate gradients

The constructions below expose the single matrix-vector product used by each recurrence
step. They are independent of the matrix, and their runs equal the library's actual states.
The CG construction takes the initial residual as input; computing it for a general initial
guess costs a further product. For zero initial guess it is simply the right-hand side.
All equalities hold at and after breakdown because the existing recurrences are total.

Sources: Trefethen--Bau (1997), Algorithms 36.1 and 38.1.
atlas: matvec-query-model (partial)
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The matrix-free part of a Lanczos step, given the response `A *ᵥ s.cur`. -/
def lanczosUpdate (s : LanczosState n) (response : n → ℝ) : LanczosState n :=
  let w := response - (s.cur ⬝ᵥ response) • s.cur - s.beta • s.prev
  ⟨s.cur, ‖WithLp.toLp 2 w‖⁻¹ • w, ‖WithLp.toLp 2 w‖⟩

/-- A `q`-query algorithm that computes the `q`-th Lanczos state. The initial vector
and every scalar operation are independent of the oracle. -/
def lanczosQueryAlgorithm (b : n → ℝ) (q : ℕ) :
    QueryAlgorithm (n → ℝ) (n → ℝ) q (LanczosState n) :=
  QueryAlgorithm.ofState (lanczosInit b) LanczosState.cur lanczosUpdate q

/-- The adaptive query implementation equals the native Lanczos recurrence for every
matrix, including nonsymmetric matrices and zero vectors. Symmetry is needed only for
the subsequent orthogonality and grade conclusions.
atlas: matvec-query-model (partial) -/
theorem run_lanczosQueryAlgorithm (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    (lanczosQueryAlgorithm b q).run (A *ᵥ ·) = lanczosState A b q := by
  rw [lanczosQueryAlgorithm, QueryAlgorithm.run_ofState]
  rfl

/-- The actual query at step `i` is the native Lanczos vector `q_i`. -/
theorem queryAt_lanczosQueryAlgorithm (A : Matrix n n ℝ) (b : n → ℝ) (q i : ℕ) :
    (lanczosQueryAlgorithm b q).queryAt (A *ᵥ ·) i = lanczosRecurrence A b i := by
  rw [lanczosQueryAlgorithm, QueryAlgorithm.queryAt_ofState]
  rfl

/-- The matrix-free part of a CG step, given the response `A *ᵥ s.p`. -/
def cgUpdate (s : CGState n) (response : n → ℝ) : CGState n :=
  let α := (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ response)
  let r' := s.r - α • response
  ⟨s.x + α • s.p, r', r' + ((r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)) • s.p⟩

/-- A `q`-query CG algorithm when the initial residual is supplied. Its construction
does not use the matrix. For a general initial guess, obtaining the supplied residual
requires one additional product; for zero initial guess it requires none. -/
def cgQueryAlgorithm (x₀ r₀ : n → ℝ) (q : ℕ) :
    QueryAlgorithm (n → ℝ) (n → ℝ) q (CGState n) :=
  QueryAlgorithm.ofState ⟨x₀, r₀, r₀⟩ CGState.p cgUpdate q

/-- With the correct supplied initial residual, the query algorithm computes precisely
the library's CG state. No positive-definiteness hypothesis is required for realization.
atlas: matvec-query-model (partial) -/
theorem run_cgQueryAlgorithm (A : Matrix n n ℝ) (c x₀ r₀ : n → ℝ)
    (hr : r₀ = c - A *ᵥ x₀) (q : ℕ) :
    (cgQueryAlgorithm x₀ r₀ q).run (A *ᵥ ·) = cgRecurrence A c x₀ q := by
  subst r₀
  rw [cgQueryAlgorithm, QueryAlgorithm.run_ofState]
  rfl

/-- Starting from zero, `q` matrix-vector queries compute the native `q`-step CG state.
The algorithm is fixed before the matrix is supplied.
atlas: matvec-query-model (partial) -/
theorem run_cgQueryAlgorithm_zero (A : Matrix n n ℝ) (c : n → ℝ) (q : ℕ) :
    (cgQueryAlgorithm 0 c q).run (A *ᵥ ·) = cgRecurrence A c 0 q :=
  run_cgQueryAlgorithm A c 0 c (by simp) q

/-- CG with one charged query for its initial residual and `q` subsequent recurrence
steps. There is no matrix-dependent value hidden in the strategy. -/
def cgInitializedQueryAlgorithm (c x₀ : n → ℝ) (q : ℕ) :
    QueryAlgorithm (n → ℝ) (n → ℝ) (q + 1) (CGState n) :=
  QueryAlgorithm.prependQuery x₀ (fun response => cgQueryAlgorithm x₀ (c - response) q)

/-- The full CG recurrence, including computation of its initial residual, has an
implementation with `q + 1` queries.
atlas: matvec-query-model (partial) -/
theorem run_cgInitializedQueryAlgorithm (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) :
    (cgInitializedQueryAlgorithm c x₀ q).run (A *ᵥ ·) = cgRecurrence A c x₀ q := by
  rw [cgInitializedQueryAlgorithm, QueryAlgorithm.run_prependQuery]
  exact run_cgQueryAlgorithm A c x₀ _ rfl q

end NLAlib
