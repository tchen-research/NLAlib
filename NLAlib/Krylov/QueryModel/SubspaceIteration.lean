import NLAlib.Krylov.QueryModel.Program
import NLAlib.Krylov.Spaces.Block

/-!
# Scalar-query realization of block subspace iteration

A multiplication of a width-`s` block uses `s` ordinary vector queries, one for each
column. Repeating it `q` times therefore uses `s * q` queries and returns `A^q Ω`.
Taking its range is free and yields the native `subspaceIterate`, including empty
blocks and loss of rank. This proves the actual scalar-query cost; a block product
is not silently charged as a single vector product.

Source: Saad (2011), Section 5.2; Golub--Van Loan (2013), Section 8.2.
atlas: matvec-query-model (partial)
-/

namespace NLAlib
namespace QueryProgram

variable {Q R : Type*}

/-- Query a finite family of vectors, recording one response per vector. -/
def family : {s : ℕ} → (Fin s → Q) → QueryProgram Q R (Fin s → R) s
  | 0, _ => .pure Fin.elim0
  | _s + 1, v => .query (v 0) (fun response =>
      map (Fin.cons response) (family (fun j => v j.succ)))

/-- A finite query family returns the oracle's values at its members. -/
@[simp] theorem run_family (f : Q → R) {s : ℕ} (v : Fin s → Q) :
    (family v).run f = fun j => f (v j) := by
  induction s with
  | zero => funext j; exact j.elim0
  | succ s ih =>
    simp only [family, run, run_map, ih]
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ j => rfl

end QueryProgram

open scoped Matrix
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] {s : ℕ}

/-- One block multiplication, implemented by `s` ordinary vector queries. -/
def blockMultiplyProgram (Ω : Matrix n (Fin s) K) :
    QueryProgram (n → K) (n → K) (Matrix n (Fin s) K) s :=
  QueryProgram.map (fun h => Matrix.of fun i j => h j i)
    (QueryProgram.family fun j => Ω.col j)

omit [DecidableEq n] in
/-- The block multiplication program has the expected matrix product as its output. -/
theorem run_blockMultiplyProgram (A : Matrix n n K) (Ω : Matrix n (Fin s) K) :
    (blockMultiplyProgram Ω).run A.mulVec = A * Ω := by
  simp only [blockMultiplyProgram, QueryProgram.run_map, QueryProgram.run_family]
  rfl

/-- `q` block steps as an interaction tree of `s * q` scalar matrix-vector queries. -/
def blockPowerProgram : (q : ℕ) → Matrix n (Fin s) K →
    QueryProgram (n → K) (n → K) (Matrix n (Fin s) K) (s * q)
  | 0, Ω => .pure Ω
  | q + 1, Ω => (blockMultiplyProgram Ω).bind (blockPowerProgram q)

/-- The repeated block program computes precisely `A^q Ω`.
atlas: matvec-query-model (partial) -/
theorem run_blockPowerProgram (A : Matrix n n K) (q : ℕ) (Ω : Matrix n (Fin s) K) :
    (blockPowerProgram q Ω).run A.mulVec = A ^ q * Ω := by
  induction q generalizing Ω with
  | zero => simp [blockPowerProgram, QueryProgram.run]
  | succ q ih =>
    rw [blockPowerProgram, QueryProgram.run_bind, run_blockMultiplyProgram, ih,
      ← Matrix.mul_assoc, ← pow_succ]

/-- The native subspace iterate is computable with `s * q` scalar matrix-vector queries.
The algorithm is chosen before the matrix, and zero width or zero steps cost zero.
atlas: matvec-query-model (partial) -/
theorem exists_matvecAlg_subspaceIterate (Ω : Matrix n (Fin s) K) (q : ℕ) :
    ∃ alg : MatvecAlg K n (Submodule K (n → K)), alg.cost = s * q ∧
      ∀ A : Matrix n n K, alg.run A = subspaceIterate A Ω q := by
  refine ⟨⟨s * q, (blockPowerProgram q Ω).map (fun B => LinearMap.range B.mulVecLin)⟩,
    rfl, ?_⟩
  intro A
  change QueryProgram.run A.mulVec _ = _
  rw [QueryProgram.run_map, run_blockPowerProgram]
  rfl

end NLAlib
