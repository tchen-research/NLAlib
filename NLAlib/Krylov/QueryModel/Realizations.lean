import NLAlib.Krylov.QueryModel.Program
import NLAlib.Krylov.QueryModel.Arnoldi
import NLAlib.Krylov.QueryModel.GMRES
import NLAlib.Krylov.QueryModel.Recurrences

/-!
# Native Krylov methods as matrix-vector interaction trees

These are uniform realization statements: the algorithm is chosen before the matrix,
has the stated query cost, and returns the library's actual iterate for every matrix.
The block subspace-iteration realization, with its scalar-query cost, is in
`QueryModel.SubspaceIteration`. Seed-indexed measurable strategies are treated in
`QueryModel.Measurable`.

Initial residuals cost one product for general initial guesses. Zero starts use their
right-hand sides directly. Arithmetic not touching the matrix is free in this model.
Source: Saad (2011), Section 6.
atlas: matvec-query-model
-/

noncomputable section
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The first `q + 1` native Arnoldi vectors are uniformly computable with `q` matvecs.
This includes the zero columns produced after breakdown.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_arnoldiMatrix (b : n → ℝ) (q : ℕ) :
    ∃ alg : MatvecAlg ℝ n (Matrix n (Fin (q + 1)) ℝ), alg.cost = q ∧
      ∀ A : Matrix n n ℝ, alg.run A = arnoldiMatrix A b (q + 1) := by
  refine ⟨MatvecAlg.ofQueryAlgorithm (arnoldiQueryAlgorithm b q), rfl, ?_⟩
  intro A
  rw [MatvecAlg.run_ofQueryAlgorithm, run_arnoldiQueryAlgorithm]

omit [DecidableEq n] in
/-- The `q`-th native Lanczos state is uniformly computable with `q` matvecs, including
the total recurrence's behavior at breakdown.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_lanczosState (b : n → ℝ) (q : ℕ) :
    ∃ alg : MatvecAlg ℝ n (LanczosState n), alg.cost = q ∧
      ∀ A : Matrix n n ℝ, alg.run A = lanczosState A b q := by
  refine ⟨MatvecAlg.ofQueryAlgorithm (lanczosQueryAlgorithm b q), rfl, ?_⟩
  intro A
  rw [MatvecAlg.run_ofQueryAlgorithm, run_lanczosQueryAlgorithm]

/-- Zero-start GMRES over either scalar field uses `q` matvecs for `q` steps.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_gmresIterate_zero {𝕜 : Type*} [RCLike 𝕜] (c : n → 𝕜) (q : ℕ) :
    ∃ alg : MatvecAlg 𝕜 n (n → 𝕜), alg.cost = q ∧
      ∀ A : Matrix n n 𝕜, alg.run A = gmresIterate A c 0 q := by
  refine ⟨MatvecAlg.ofQueryAlgorithm (gmresQueryAlgorithm 0 c q), rfl, ?_⟩
  intro A
  rw [MatvecAlg.run_ofQueryAlgorithm, run_gmresQueryAlgorithm_zero]

/-- GMRES with an arbitrary initial guess includes the query for its initial residual.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_gmresIterate {𝕜 : Type*} [RCLike 𝕜] (c x₀ : n → 𝕜) (q : ℕ) :
    ∃ alg : MatvecAlg 𝕜 n (n → 𝕜), alg.cost = q + 1 ∧
      ∀ A : Matrix n n 𝕜, alg.run A = gmresIterate A c x₀ q := by
  refine ⟨MatvecAlg.ofQueryAlgorithm (gmresInitializedQueryAlgorithm c x₀ q), rfl, ?_⟩
  intro A
  rw [MatvecAlg.run_ofQueryAlgorithm, run_gmresInitializedQueryAlgorithm]

omit [DecidableEq n] in
/-- Zero-start conjugate gradients uses `q` matvecs for its actual `q`-step state.
No positive-definiteness hypothesis is needed for the realization equality.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_cgRecurrence_zero (c : n → ℝ) (q : ℕ) :
    ∃ alg : MatvecAlg ℝ n (CGState n), alg.cost = q ∧
      ∀ A : Matrix n n ℝ, alg.run A = cgRecurrence A c 0 q := by
  refine ⟨MatvecAlg.ofQueryAlgorithm (cgQueryAlgorithm 0 c q), rfl, ?_⟩
  intro A
  rw [MatvecAlg.run_ofQueryAlgorithm, run_cgQueryAlgorithm_zero]

omit [DecidableEq n] in
/-- CG with an arbitrary initial guess charges for the initial residual and every step.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_cgRecurrence (c x₀ : n → ℝ) (q : ℕ) :
    ∃ alg : MatvecAlg ℝ n (CGState n), alg.cost = q + 1 ∧
      ∀ A : Matrix n n ℝ, alg.run A = cgRecurrence A c x₀ q := by
  refine ⟨MatvecAlg.ofQueryAlgorithm (cgInitializedQueryAlgorithm c x₀ q), rfl, ?_⟩
  intro A
  rw [MatvecAlg.run_ofQueryAlgorithm, run_cgInitializedQueryAlgorithm]

end NLAlib
