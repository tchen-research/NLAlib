import NLAlib.Krylov.QueryModel.Iteration
import NLAlib.Krylov.Spaces.Matrix

/-!
# Computing Krylov generators through matrix-vector queries

Successive powers require one additional product each. The transcript records
`A b, ..., A^q b`, so both `K_q`'s generator matrix and its image under `A` can
be reconstructed without any further access to the matrix.
Source: Saad (2003), Sections 6.1 and 6.5.
atlas: matvec-query-model (partial)
-/

open scoped Matrix
namespace NLAlib

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Successive matrix-vector powers, implemented without access to the matrix. -/
def powerQueryAlgorithm (b : n → K) (q : ℕ) :
    QueryAlgorithm (n → K) (n → K) q (n → K) :=
  QueryAlgorithm.ofState b id (fun _ response => response) q

private theorem iterate_mulVec_eq_pow (A : Matrix n n K) (b : n → K) (q : ℕ) :
    (fun x => A *ᵥ x)^[q] b = A ^ q *ᵥ b := by
  induction q with
  | zero => simp
  | succ q ih => rw [Function.iterate_succ_apply', ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- Exactly `q` successive query rounds produce `A^q b`. -/
theorem run_powerQueryAlgorithm (A : Matrix n n K) (b : n → K) (q : ℕ) :
    (powerQueryAlgorithm b q).run (A *ᵥ ·) = A ^ q *ᵥ b := by
  rw [powerQueryAlgorithm, QueryAlgorithm.run_ofState]
  exact iterate_mulVec_eq_pow A b q

/-- The next queried vector is the corresponding Krylov power. -/
theorem queryAt_powerQueryAlgorithm (A : Matrix n n K) (b : n → K) (q i : ℕ) :
    (powerQueryAlgorithm b q).queryAt (A *ᵥ ·) i = A ^ i *ᵥ b := by
  rw [powerQueryAlgorithm, QueryAlgorithm.queryAt_ofState]
  exact iterate_mulVec_eq_pow A b i

/-- The transcript consists of the powers `A b` through `A^q b`. -/
theorem transcript_powerQueryAlgorithm (A : Matrix n n K) (b : n → K)
    (q : ℕ) (j : Fin q) :
    (powerQueryAlgorithm b q).transcript (A *ᵥ ·) j = A ^ ((j : ℕ) + 1) *ᵥ b := by
  rw [QueryAlgorithm.transcript, QueryAlgorithm.history_apply, queryAt_powerQueryAlgorithm,
    Matrix.mulVec_mulVec, ← pow_succ']

/-- Recover the matrix `[b, A b, ..., A^(q-1) b]` from `q` responses. -/
def krylovMatrixFromTranscript (b : n → K) {q : ℕ} (h : Fin q → n → K) :
    Matrix n (Fin q) K := fun i j =>
  if hj : (j : ℕ) = 0 then b i else h ⟨(j : ℕ) - 1, by omega⟩ i

/-- Reconstructing generators from the actual transcript gives the native Krylov matrix. -/
theorem krylovMatrixFromTranscript_eq (A : Matrix n n K) (b : n → K) (q : ℕ) :
    krylovMatrixFromTranscript b ((powerQueryAlgorithm b q).transcript (A *ᵥ ·)) =
      krylovMatrix A b q := by
  ext i j
  simp only [krylovMatrixFromTranscript, krylovMatrix]
  split_ifs with hj
  · simp [hj]
  · rw [transcript_powerQueryAlgorithm]
    congr 3
    exact Nat.sub_add_cancel (by omega)

/-- The response matrix is exactly `A` times the Krylov generator matrix. -/
theorem responseMatrix_powerQueryAlgorithm (A : Matrix n n K) (b : n → K) (q : ℕ) :
    (fun i j => (powerQueryAlgorithm b q).transcript (A *ᵥ ·) j i) =
      A * krylovMatrix A b q := by
  ext i j
  rw [transcript_powerQueryAlgorithm, mul_krylovMatrix_apply]

end NLAlib
