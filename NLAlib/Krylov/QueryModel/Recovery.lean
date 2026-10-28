import NLAlib.Krylov.QueryModel.SubspaceIteration

/-!
# Exact matrix recovery from its coordinate-vector products

Querying each coordinate vector recovers every matrix column. This is an
oracle-query statement; it makes no claim about the arithmetic cost of later
postprocessing, such as computing an empirical spectral law.
-/

noncomputable section
namespace NLAlib
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Recover a matrix with one scalar vector query for every coordinate. -/
def matrixRecoveryProgram :
    QueryProgram (n → K) (n → K) (Matrix n n K) (Fintype.card n) :=
  (QueryProgram.family (fun j : Fin (Fintype.card n) =>
    Pi.single ((Fintype.equivFin n).symm j) (1 : K))).map
    (fun responses => Matrix.of fun i j => responses (Fintype.equivFin n j) i)

/-- The coordinate queries recover the input matrix exactly. -/
@[simp] theorem run_matrixRecoveryProgram (A : Matrix n n K) :
    matrixRecoveryProgram.run A.mulVec = A := by
  simp only [matrixRecoveryProgram, QueryProgram.run_map, QueryProgram.run_family,
    Matrix.mulVec_single_one, Equiv.symm_apply_apply]
  rfl

/-- Every oracle-free matrix function can be evaluated after `card n` queries. -/
theorem exists_matvecAlg_apply_of_matrixRecovery {β : Type*} (f : Matrix n n K → β) :
    ∃ alg : MatvecAlg K n β, alg.cost = Fintype.card n ∧ ∀ A, alg.run A = f A := by
  refine ⟨⟨_, matrixRecoveryProgram.map f⟩, rfl, ?_⟩
  intro A
  simpa only [MatvecAlg.run, QueryProgram.run_map] using congrArg f (run_matrixRecoveryProgram A)

end NLAlib
