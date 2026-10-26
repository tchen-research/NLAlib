import NLAlib.Krylov.QueryModel.Iteration

/-!
# Bounded interaction trees and their transcript semantics

`QueryProgram` is the syntax of a finite interaction tree: a leaf is an output,
and an internal node asks one query and continues with its response. The type index
records the exact number of query rounds on every branch. A shorter computation can
be padded with zero queries for a matrix oracle. `QueryAlgorithm.toProgram` compiles
the finite-history representation to this syntax and preserves its semantics.

Source: Saad (2011), Section 6, operation counts in the matrix-vector access model.
atlas: matvec-query-model (partial)
-/

namespace NLAlib

/-- A finite interaction tree with exactly `q` oracle queries on every branch. -/
inductive QueryProgram (Q R β : Type*) : ℕ → Type _
  | pure (value : β) : QueryProgram Q R β 0
  | query {q : ℕ} (value : Q) (next : R → QueryProgram Q R β q) : QueryProgram Q R β (q + 1)

namespace QueryProgram

variable {Q R α β : Type*} {q r : ℕ}

/-- Answer each query using the supplied oracle. -/
def run (f : Q → R) : {q : ℕ} → QueryProgram Q R β q → β
  | _, .pure value => value
  | _, .query value next => run f (next (f value))

/-- Free postprocessing of the result leaves the query budget unchanged. -/
def map (g : α → β) : {q : ℕ} → QueryProgram Q R α q → QueryProgram Q R β q
  | _, .pure value => .pure (g value)
  | _, .query value next => .query value (fun response => map g (next response))

/-- Postprocessing has the expected oracle semantics. -/
@[simp] theorem run_map (f : Q → R) (g : α → β) (p : QueryProgram Q R α q) :
    run f (map g p) = g (run f p) := by
  induction p with
  | pure value => rfl
  | query value next ih => exact ih (f value)

/-- Sequential composition adds the two query budgets. -/
def bind : {q : ℕ} → QueryProgram Q R α q →
    (α → QueryProgram Q R β r) → QueryProgram Q R β (r + q)
  | _, .pure value, next => next value
  | _, .query value branch, next => .query value (fun response => bind (branch response) next)

/-- Running a sequential composition first runs the initial tree, then its continuation. -/
@[simp] theorem run_bind (f : Q → R) (p : QueryProgram Q R α q)
    (next : α → QueryProgram Q R β r) :
    run f (bind p next) = run f (next (run f p)) := by
  induction p with
  | pure value => rfl
  | query value branch ih => exact ih (f value)

end QueryProgram

namespace QueryAlgorithm

variable {Q R β : Type*}

/-- The strategy remaining after its first response is known. -/
def afterFirst {q : ℕ} (alg : QueryAlgorithm Q R (q + 1) β) (response : R) :
    QueryAlgorithm Q R q β where
  query i h := alg.query (i + 1) (Fin.cons response h)
  output h := alg.output (Fin.cons response h)

/-- Separating the first query from the remaining strategy preserves the strategy. -/
theorem prependQuery_afterFirst {q : ℕ} (alg : QueryAlgorithm Q R (q + 1) β) :
    prependQuery (alg.query 0 Fin.elim0) alg.afterFirst = alg := by
  cases alg with
  | mk query output =>
    simp only [prependQuery, afterFirst]
    congr 1
    · funext i h
      cases i with
      | zero => exact congrArg (query 0) (funext fun j => j.elim0)
      | succ i =>
        change query (i + 1) (Fin.cons (h 0) (Fin.tail h)) = query (i + 1) h
        rw [Fin.cons_self_tail]
    · funext h
      change output (Fin.cons (h 0) (Fin.tail h)) = output h
      rw [Fin.cons_self_tail]

/-- Compile a finite-history strategy to a bounded interaction tree. -/
def toProgram : {q : ℕ} → QueryAlgorithm Q R q β → QueryProgram Q R β q
  | 0, alg => .pure (alg.output Fin.elim0)
  | _q + 1, alg => .query (alg.query 0 Fin.elim0) (fun response => toProgram (alg.afterFirst response))

/-- The interaction tree answers exactly the same queries and returns the same output
as its finite-history strategy.
atlas: matvec-query-model (partial) -/
theorem run_toProgram {q : ℕ} (alg : QueryAlgorithm Q R q β) (f : Q → R) :
    alg.toProgram.run f = alg.run f := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change (alg.afterFirst (f (alg.query 0 Fin.elim0))).toProgram.run f = _
    rw [ih, ← run_prependQuery, prependQuery_afterFirst]

end QueryAlgorithm

/-- A matrix-vector algorithm with a finite query budget, over arbitrary scalar entries. -/
def MatvecAlg (𝕜 n β : Type*) := Σ q : ℕ, QueryProgram (n → 𝕜) (n → 𝕜) β q

namespace MatvecAlg

/-- Regard a finite-history strategy as an interaction tree with the same query budget. -/
def ofQueryAlgorithm {𝕜 n β : Type*} {q : ℕ}
    (alg : QueryAlgorithm (n → 𝕜) (n → 𝕜) q β) : MatvecAlg 𝕜 n β :=
  ⟨q, alg.toProgram⟩

/-- The number of matrix-vector query rounds. -/
def cost {𝕜 n β : Type*} (alg : MatvecAlg 𝕜 n β) : ℕ := alg.1

/-- Semantics of a matrix-vector interaction tree on a supplied matrix. -/
def run {𝕜 n β : Type*} [Fintype n] [NonUnitalNonAssocSemiring 𝕜]
    (alg : MatvecAlg 𝕜 n β) (A : Matrix n n 𝕜) : β :=
  alg.2.run A.mulVec

/-- Compiling a strategy preserves its charged query budget. -/
@[simp] theorem cost_ofQueryAlgorithm {𝕜 n β : Type*} {q : ℕ}
    (alg : QueryAlgorithm (n → 𝕜) (n → 𝕜) q β) : (ofQueryAlgorithm alg).cost = q := rfl

/-- Compiling a strategy preserves its matrix-vector semantics. -/
@[simp] theorem run_ofQueryAlgorithm {𝕜 n β : Type*} [Fintype n]
    [NonUnitalNonAssocSemiring 𝕜] {q : ℕ}
    (alg : QueryAlgorithm (n → 𝕜) (n → 𝕜) q β) (A : Matrix n n 𝕜) :
    (ofQueryAlgorithm alg).run A = alg.run A.mulVec := alg.run_toProgram A.mulVec

end MatvecAlg
end NLAlib
